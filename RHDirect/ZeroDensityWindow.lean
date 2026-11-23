import RHDirect.Interfaces

/-!
# RHDirect.ZeroDensityWindow

Compact, direct, zero-`sorry`, zero-custom-`axiom` rebuild of the **Explicit Formula Error,
Mean-Square, Zero-Density Bad-Prime Counting & Quantitative Window-Coupling Bridge**
(`TopPlug` / `TopShape` / `ε < 1/52` → `AllLevelsWindowBound (3/2)`).

This module bridges Pillar 2 (`RHDirect.ThetaSlopeEngine` / `RHDirect.SlopeInequality`)
directly into Pillar 1 (`RHDirect.AnalyticBridge` / `RHDirect.LandauWindow`):

1. **Quantitative Exponent & Window Arithmetic**:
   - `ε < 1 / 52 ↔ 13 * ε < 1 / 4`, `377 = 1 + 47 * 8`, `40000 = 37700 + 2267 + 33`,
     `cTop7 eD eL = max (eD + 1) (max (eL + 2) 3)` with `cTop7 2 0 = 3`,
   - explicit constructive `log`-vs-`rpow` decay (`A * log Y ≤ Y ^ δ`) and
     `exp (-c * √(log x)) ≤ 24 / c^4 / (log x)^2`,
   - window restriction `[Y, Y^(3/2)] ⊆ [Y, Y^2]` for `1 ≤ Y` (`la = 3 / 2`).
2. **Wave-Grid & Exceptional-Rank Envelope (`NWvBound`, `EventuallyRankLeRpowOfLtOneDivFiftytwo`)**:
   - explicit bounds `nWv R s ≤ 5288 * Y^2267`, `TOv s ≤ 2 * Y^37700` (`Y = x^(1/100)`),
   - `eventually_rank_t_le_rpow_400`: `0 < ε < 1 / 52 → x ≥ 2^100 → (R.t : ℝ) ≤ x ^ 400`,
     embedding cleanly into the `VWin` Selmer cutoff `⌊x ^ 401⌋₊`.
3. **Mean-Square Character Bounds & Zero-Density Bad-Prime Counting (`MeanSquareBounds`)**:
   - exact quadratic expansion `meansq_expand` and diagonal / exceptional / off-diagonal
     splitting `meansq_split` for weighted character sums (including Jacobi symbols),
   - weighted von Mangoldt sum bound `sum_cN_le_of_mertens`,
   - Chebyshev/Markov bad-set extraction `chebyshev_bad_card` & `share_of_bad`,
   - zero-density box bad-prime counting `count_bad_of_zeroDensityBox` (`|S| ≤ C * Q^(1/4)`),
   - two-stage prime-pair good-share extraction `pair_share_of_stages`.
4. **Explicit Formula Error Bracket & Window-Coupling Calculus (`SChain`, `GrowthBracketBoundOfSizeWindows`)**:
   - exact `Nc` identity and division of `errorBracketSizeWindows` under `RestSize`,
   - both the tight `m ∈ [x^(1/2 - ε/8), x^(1/2)]` bracket (`24 ≤ x^(7ε/8)`) and the full
     `RestSize` bracket `m ∈ [x^(1/2 - ε), x^(1/2 + ε/2)]` (`3 ≤ x`, `26 ≤ x^(3ε/8)`),
   - explicit-formula log-derivative transfer `explicitFormula_logDeriv_transfer`,
   - sharp conversion of bracket inequalities into `Gx ≤ x ^ (1/2 + (C + 3) * ε)`.
5. **`TopShape` / `TopPlug` Window-Coupling Bridge (`ε < 1/52` → `AllLevelsWindowBound (3/2)`)**:
   - `levelWindowBound_of_bracket_windows`: quantitative `ε < 1/52` bracket windows on
     `[Y, Y^(3/2)]` directly yield `LevelWindowBound L (3/2)`,
   - `levelWindowBound_three_halves_of_square_windows`: restricting `[Y, Y^2]` windows
     to `[Y, Y^(3/2)]`,
   - `allLevelsWindowBound_three_halves_of_brackets`, `topPlug_thetaSlopeContract`, and
     `topPlug_zeroFreeAll` directly connecting `VWin S` + `AnalyticBridgeContract` to `ZeroFreeAll`.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt
open Finset

namespace RHDirect
namespace ZeroDensityWindow

/-! ## 1. Quantitative Exponent Arithmetic (`ε < 1/52`, `377 = 1 + 47 * 8`, `la = 3/2`) -/

/-- The critical `ε < 1 / 52` threshold is equivalent to `13 * ε < 1 / 4`. -/
theorem eps_lt_one_div_52_iff (ε : ℝ) : ε < 1 / 52 ↔ 13 * ε < 1 / 4 := by
  constructor <;> intro h <;> linarith

/-- Key arithmetic identities governing `TOv`, `nWv`, and the `400 / 401` rank ceiling. -/
theorem rank_exponent_identities :
    377 = 1 + 47 * 8 ∧ 37700 + 2267 + 33 = 40000 ∧ (10708 : ℝ) ≤ (2 : ℝ) ^ 33 := by
  norm_num

/-- Joint error exponent `cTop7 eD eL = max (eD + 1) (max (eL + 2) 3)`. -/
def cTop7 (eD eL : ℝ) : ℝ := max (eD + 1) (max (eL + 2) 3)

theorem cTop7_two_zero : cTop7 2 0 = 3 := by
  unfold cTop7
  norm_num

theorem cTop7_eq_three {eD eL : ℝ} (hD : eD ≤ 2) (hL : eL ≤ 1) : cTop7 eD eL = 3 := by
  unfold cTop7
  have h1 : eL + 2 ≤ 3 := by linarith
  have h2 : eD + 1 ≤ 3 := by linarith
  rw [max_eq_right h1, max_eq_right h2]

theorem three_le_cTop7 (eD eL : ℝ) : 3 ≤ cTop7 eD eL :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem cTop7_mono {eD eL eD' eL' : ℝ} (hD : eD ≤ eD') (hL : eL ≤ eL') :
    cTop7 eD eL ≤ cTop7 eD' eL' := by
  unfold cTop7
  exact max_le_max (by linarith) (max_le_max (by linarith) le_rfl)

theorem cTop7_le_add_three {eD eL : ℝ} (hD : 0 ≤ eD) (hL : 0 ≤ eL) :
    cTop7 eD eL ≤ eD + eL + 3 := by
  unfold cTop7
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

/-- For any `θ > 1 / 2` and any error exponent `C ≥ 0`, there exists `0 < ε < 1 / 52`
such that `13 * ε < 1 / 4` and `1 / 2 + (C + 3) * ε < θ`. -/
theorem exists_eps_lt_one_div_52_for_theta {θ C : ℝ} (hθ : 1 / 2 < θ) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 52 ∧ 13 * ε < 1 / 4 ∧ 1 / 2 + (C + 3) * ε < θ := by
  let ε := min (1 / 104 : ℝ) ((θ - 1 / 2) / (2 * (C + 3)))
  have hC3 : 0 < C + 3 := by linarith
  have hpos : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have h52 : ε < 1 / 52 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have h13 : 13 * ε < 1 / 4 := (eps_lt_one_div_52_iff ε).mp h52
  have hle : ε ≤ (θ - 1 / 2) / (2 * (C + 3)) := min_le_right _ _
  have hmul : (C + 3) * ε ≤ (θ - 1 / 2) / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hle hC3.le
    have h2 : (C + 3) * ((θ - 1 / 2) / (2 * (C + 3))) = (θ - 1 / 2) / 2 := by
      field_simp [hC3.ne']
    linarith
  exact ⟨ε, hpos, h52, h13, by linarith⟩

/-- Explicit constructive `log`-vs-`rpow` dominance: `A * log Y ≤ Y ^ δ` for all
`Y ≥ max 1 ((2 * A / δ) ^ (2 / δ))`. -/
theorem mul_log_le_rpow_of_ge {δ A Y : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hY : max 1 ((2 * A / δ) ^ (2 / δ)) ≤ Y) :
    A * Real.log Y ≤ Y ^ δ := by
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hY0 : 0 < Y := by linarith
  have hY2 : (2 * A / δ) ^ (2 / δ) ≤ Y := le_trans (le_max_right _ _) hY
  have hhalf : 0 < δ / 2 := by linarith
  have hlog : Real.log (Y ^ (δ / 2)) ≤ Y ^ (δ / 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hY0 (δ / 2))
    linarith
  rw [Real.log_rpow hY0] at hlog
  have hcoeff : 2 * A / δ ≤ Y ^ (δ / 2) := by
    have hpos : 0 < 2 * A / δ := by positivity
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hpos.le _) hY2 hhalf.le
    rw [← Real.rpow_mul hpos.le] at hpow
    have hmul : (2 / δ) * (δ / 2) = 1 := by field_simp [hδ.ne']
    rw [hmul, Real.rpow_one] at hpow
    exact hpow
  have hstep1 : A * Real.log Y ≤ (2 * A / δ) * Y ^ (δ / 2) := by
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * A / δ by positivity)
    have hEq : (2 * A / δ) * (δ / 2 * Real.log Y) = A * Real.log Y := by
      field_simp [hδ.ne']
    linarith
  calc A * Real.log Y
      ≤ (2 * A / δ) * Y ^ (δ / 2) := hstep1
    _ ≤ Y ^ (δ / 2) * Y ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hY0.le _)
    _ = Y ^ (δ / 2 + δ / 2) := (Real.rpow_add hY0 _ _).symm
    _ = Y ^ δ := by ring_nf

/-- Elementary log-to-sqrt bounds used in `meanSqK`:
`log y ≤ 2 * √y` and `w * log y ≤ 4 * √y` for `1 ≤ y` and `w ≤ y ^ (1/5)`. -/
theorem log_and_mul_log_le_sqrt {y w : ℝ} (hy : 1 ≤ y)
    (hw : w ≤ y ^ (1 / 5 : ℝ)) :
    Real.log y ≤ 2 * Real.sqrt y ∧ w * Real.log y ≤ 4 * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have key : ∀ a : ℝ, 0 < a → a * Real.log y ≤ y ^ a := by
    intro a ha
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 a)
    rw [Real.log_rpow hy0] at h
    linarith
  have hsq : Real.sqrt y = y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  constructor
  · have h := key (1 / 2) (by norm_num)
    rw [hsq]
    linarith
  · have h3 := key (3 / 10) (by norm_num)
    have h3' : Real.log y ≤ 10 / 3 * y ^ (3 / 10 : ℝ) := by linarith
    have hmul : y ^ (1 / 5 : ℝ) * y ^ (3 / 10 : ℝ) = Real.sqrt y := by
      rw [← Real.rpow_add hy0, hsq]
      norm_num
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    calc w * Real.log y
        ≤ y ^ (1 / 5 : ℝ) * (10 / 3 * y ^ (3 / 10 : ℝ)) :=
          mul_le_mul hw h3' hl (Real.rpow_nonneg hy0.le _)
      _ = 10 / 3 * Real.sqrt y := by rw [← hmul]; ring
      _ ≤ 4 * Real.sqrt y := by linarith

/-- Explicit Siegel–Walfisz tail domination from `GIntegral.lean`:
`exp (-c * √(log x)) ≤ 24 / c^4 / (log x)^2` for `c > 0` and `x > 1`. -/
theorem exp_neg_sqrt_log_le {c x : ℝ} (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / c ^ 4 / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs : 0 < c * Real.sqrt (Real.log x) := mul_pos hc (Real.sqrt_pos.mpr hL)
  have h4 : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL.le]
  have hexp := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x)) hs.le 4
  rw [h4] at hexp
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  rw [neg_mul, Real.exp_neg, div_div,
    inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact hexp

/-- For `1 ≤ Y`, the `la = 3/2` window `[Y, Y^(3/2)]` sits inside the square window `[Y, Y^2]`. -/
theorem Icc_three_halves_subset_square {Y : ℝ} (hY : 1 ≤ Y) :
    Set.Icc Y (Y ^ (3 / 2 : ℝ)) ⊆ Set.Icc Y (Y ^ (2 : ℝ)) := by
  intro y hy
  refine ⟨hy.1, le_trans hy.2 ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

/-! ## 2. Wave-Grid & Exceptional-Rank Envelope (`NWvBound` & `ε < 1/52 → R.t ≤ x^400`) -/

/-- Exact structural relations on `(s : ScaleParams)` and `(R : ChainRanks)` matching
the upstream `Scale` and `Ranks` definitions for `EventuallyRankLeRpowOfLtOneDivFiftytwo`. -/
structure RankScaleHyps (s : ScaleParams) (R : ChainRanks) : Prop where
  rankVal : RankVal s R
  f_eq : R.f = 2 * R.n
  two_le_m : 2 ≤ R.m
  m_add_three_le_k : R.m + 3 ≤ R.k
  r_le_two_k : R.r ≤ 2 * R.k
  delta1_eq : s.delta1 = s.x ^ (-(s.eps / 8))
  L_eq : s.L = s.x ^ s.eps

/-- Explicit `nWv`, `TOv`, and `R.t ≤ x ^ 400` bounds for `0 < ε < 1 / 52` and `2 ^ 100 ≤ s.x`. -/
theorem nWv_TOv_rank_t_bounds {s : ScaleParams} {R : ChainRanks}
    (hx : (2 : ℝ) ^ 100 ≤ s.x) (hRS : RankScaleHyps s R) :
    (nWv R s : ℝ) ≤ 5288 * (s.x ^ ((1 : ℝ) / 100)) ^ 2267 ∧
    (TOv s : ℝ) ≤ 2 * (s.x ^ ((1 : ℝ) / 100)) ^ 37700 ∧
    (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  have hX1 : 1 < s.x := s.x_gt_one
  have hX0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  obtain ⟨⟨-, hn2⟩, ⟨hm1, -⟩, ⟨-, hk2⟩, heq⟩ := hRS.rankVal
  have hmono : ∀ a b : ℝ, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hY : ∀ n : ℕ, s.x ^ ((n : ℝ) / 100) = (s.x ^ ((1 : ℝ) / 100)) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    ring_nf
  have hY2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 100) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ 100) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have h2 : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  set Y : ℝ := s.x ^ ((1 : ℝ) / 100)
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hn : (R.n : ℝ) ≤ 2 * Y ^ 216 := by
    have h := hmono _ _ (show 2 + 8 * s.eps ≤ ((216 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hfe : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    have := hRS.f_eq
    exact_mod_cast this
  have hf : (R.f : ℝ) ≤ 4 * Y ^ 216 := by linarith
  have hk : (R.k : ℝ) ≤ 2 * Y ^ 470 := by
    have h := hmono _ _ (show 9 / 2 + 10 * s.eps ≤ ((470 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hm : Y ^ 49 ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm1
    rw [Real.le_sqrt (by positivity) (mul_nonneg hX0.le s.delta1_pos.le)]
    have h1 : (Y ^ 49) ^ 2 = s.x ^ (((98 : ℕ) : ℝ) / 100) := by rw [hY]; ring
    have h2 : s.x * s.delta1 = s.x ^ ((1 : ℝ) + -(s.eps / 8)) := by
      rw [hRS.delta1_eq, Real.rpow_add hX0, Real.rpow_one]
    rw [h1, h2]
    exact hmono _ _ (by push_cast; linarith)
  have hm0 : (0 : ℝ) < R.m := lt_of_lt_of_le (by positivity) hm
  have hL : s.L ^ 2 ≤ Y ^ 4 := by
    have h1 : s.L ^ 2 = s.x ^ (s.eps * 2) := by
      rw [hRS.L_eq, Real.rpow_mul hX0.le, Real.rpow_two]
    rw [h1]
    have h := hmono _ _ (show s.eps * 2 ≤ ((4 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    exact h
  have hr : (R.r : ℝ) ≤ 4 * Y ^ 470 := by
    have h' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast hRS.r_le_two_k
    linarith
  have hk5 : (5 : ℝ) ≤ R.k := by
    have h1 := hRS.m_add_three_le_k
    have h2 := hRS.two_le_m
    exact_mod_cast (by omega : 5 ≤ R.k)
  have hk0 : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
  have hk' : (R.k : ℝ) - 1 ≤ 2 * Y ^ 470 := by linarith
  have hB : (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 128 * Y ^ 1797 := by
    rw [div_le_iff₀ hm0]
    calc (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2
        ≤ (4 * Y ^ 216) ^ 2 * (2 * Y ^ 470) ^ 3 * Y ^ 4 := by gcongr
      _ = 128 * Y ^ 1797 * Y ^ 49 := by ring
      _ ≤ 128 * Y ^ 1797 * R.m := by gcongr
  have hp1 : Y ^ 216 ≤ Y ^ 1797 := pow_le_pow_right₀ hY1 (by norm_num)
  have hQ : (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 132 * Y ^ 1797 := by
    linarith
  have hQ0 : 0 ≤ (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have hBq : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hk0 3)) (by positivity))
        hm0.le
    linarith [Nat.cast_nonneg (α := ℝ) R.f]
  have hr0 : (0 : ℝ) ≤ R.r := Nat.cast_nonneg _
  have hW : (nWv R s : ℝ) ≤ 5288 * Y ^ 2267 := by
    have hy0 : (0 : ℝ) ≤
        10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 :=
      div_nonneg (mul_nonneg (by positivity) hQ0) (by norm_num)
    have hc := Nat.ceil_lt_add_one hy0
    have hyb : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m)
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
  refine ⟨hW, hT, ?_⟩
  have heqR : (R.r : ℝ) + R.t = 8 * R.f * R.r + 4 + (TOv s : ℝ) * (nWv R s : ℝ) := by
    exact_mod_cast heq
  have hfr : (R.f : ℝ) * R.r ≤ (4 * Y ^ 216) * (4 * Y ^ 470) :=
    mul_le_mul hf hr hr0 (by positivity)
  have hTW : (TOv s : ℝ) * nWv R s ≤ (2 * Y ^ 37700) * (5288 * Y ^ 2267) :=
    mul_le_mul hT hW (by positivity) (by positivity)
  rw [show (400 : ℝ) = ((40000 : ℕ) : ℝ) / 100 by norm_num, hY]
  have e1 : (4 * Y ^ 216) * (4 * Y ^ 470) = 16 * Y ^ 686 := by ring
  have e2 : (2 * Y ^ 37700) * (5288 * Y ^ 2267) = 10576 * Y ^ 39967 := by ring
  have p1 : Y ^ 686 ≤ Y ^ 39967 := pow_le_pow_right₀ hY1 (by norm_num)
  have p2 : (1 : ℝ) ≤ Y ^ 39967 := one_le_pow₀ hY1
  have p3 : (10708 : ℝ) ≤ Y ^ 33 := by
    have := pow_le_pow_left₀ (by norm_num) hY2 33
    norm_num at this
    linarith
  have e3 : Y ^ 40000 = Y ^ 33 * Y ^ 39967 := by ring
  have p4 : (10708 : ℝ) * Y ^ 39967 ≤ Y ^ 33 * Y ^ 39967 :=
    mul_le_mul_of_nonneg_right p3 (by positivity)
  rw [e3]
  linarith

/-- Eventual rank bound `R.t ≤ x ^ 400` for any `0 < ε < 1 / 52`, matching
`UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo`. -/
theorem eventually_rank_t_le_rpow_400 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ x₀ : ℝ, ∀ (s : ScaleParams) (R : ChainRanks),
        s.eps = ε → x₀ ≤ s.x → RankScaleHyps s R → (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  intro ε _ _
  refine ⟨(2 : ℝ) ^ 100, fun s R _ hx hRS => (nWv_TOv_rank_t_bounds hx hRS).2.2⟩

/-- Embedding `R.t ≤ x ^ 400` strictly inside the `VWin` Selmer cutoff `⌊x ^ 401⌋₊`
for `x ≥ 2`. -/
theorem rank_t_lt_vwin_cutoff {x : ℝ} {t : ℕ} (hx : 2 ≤ x) (ht : (t : ℝ) ≤ x ^ (400 : ℝ)) :
    t < ⌊x ^ (401 : ℝ)⌋₊ := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h400 : 1 ≤ x ^ (400 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hmul : x ^ (401 : ℝ) = x ^ (400 : ℝ) * x := by
    calc x ^ (401 : ℝ) = x ^ ((400 : ℝ) + 1) := by norm_num
      _ = x ^ (400 : ℝ) * x ^ (1 : ℝ) := Real.rpow_add hx0 _ _
      _ = x ^ (400 : ℝ) * x := by rw [Real.rpow_one]
  have hlt : (t : ℝ) + 1 ≤ x ^ (401 : ℝ) := by
    rw [hmul]
    nlinarith
  exact Nat.lt_floor_add_one (x ^ (401 : ℝ)) |> fun _ => by
    have hnat : t + 1 ≤ ⌊x ^ (401 : ℝ)⌋₊ :=
      Nat.le_floor (by exact_mod_cast hlt)
    omega

/-! ## 3. Mean-Square Bounds, Markov Bad-Set Extraction & Zero-Density Counting -/

/-- Weighted von Mangoldt coefficient `cN y n = Λ(n) * min 1 (y / n)` from `MeanSquareBounds`. -/
def cN (y : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (y / n)

theorem cN_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : 0 ≤ cN y n := by
  unfold cN
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
  exact le_min zero_le_one (div_nonneg hy (Nat.cast_nonneg _))

/-- Weighted von Mangoldt sum bound `∑_{n=1}^{⌊Z⌋} cN y n ≤ C * y * log Z` from a
Mertens sum bound `∑_{n=1}^{⌊Z⌋} Λ(n)/n ≤ C * log Z` (`SumCNLe.lean`). -/
theorem sum_cN_le_of_mertens {C y Z : ℝ} (hy : 0 ≤ y)
    (hM : ∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log Z) :
    ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
      ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * ((Λ n : ℝ) / (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro n _
        unfold cN
        calc (Λ n : ℝ) * min 1 (y / n)
            ≤ (Λ n : ℝ) * (y / n) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) ArithmeticFunction.vonMangoldt_nonneg
          _ = y * ((Λ n : ℝ) / (n : ℝ)) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, (Λ n : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left hM hy
    _ = C * y * Real.log Z := by ring

/-- Exact quadratic expansion of a character mean square over a finite set `P`
(`MeanSqAbs.lean` / `meansq_expand`): for nonnegative weights `c`, unit-bounded phases `κ`,
and integer-valued characters `χ n q`,
`∑_{q ∈ P} ‖∑_{n ∈ I} c(n) κ(n) χ(n, q)‖² ≤ ∑_{n, n' ∈ I} c(n) c(n') |∑_{q ∈ P} χ(n, q) χ(n', q)|`. -/
theorem meansq_expand {α β : Type*} (P : Finset α) (I : Finset β)
    (c : β → ℝ) (hc : ∀ n ∈ I, 0 ≤ c n)
    (κ : β → ℂ) (hκ : ∀ n ∈ I, ‖κ n‖ ≤ 1)
    (χ : β → α → ℤ) :
    ∑ q ∈ P, ‖∑ n ∈ I, (c n : ℂ) * κ n * ((χ n q : ℤ) : ℂ)‖ ^ 2 ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ)| := by
  have hsq : ∀ q ∈ P,
      ‖∑ n ∈ I, (c n : ℂ) * κ n * ((χ n q : ℤ) : ℂ)‖ ^ 2 =
        (∑ n ∈ I, ∑ n' ∈ I,
          ((c n : ℂ) * κ n * ((χ n q : ℤ) : ℂ)) *
            starRingEnd ℂ ((c n' : ℂ) * κ n' * ((χ n' q : ℤ) : ℂ))).re := by
    intro q _
    set z : ℂ := ∑ n ∈ I, (c n : ℂ) * κ n * ((χ n q : ℤ) : ℂ)
    have h1 : (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [← h1]
    congr 1
    simp only [z, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl hsq]
  rw [← Complex.re_sum]
  have hswap :
      ∑ q ∈ P, ∑ n ∈ I, ∑ n' ∈ I,
          ((c n : ℂ) * κ n * ((χ n q : ℤ) : ℂ)) *
            starRingEnd ℂ ((c n' : ℂ) * κ n' * ((χ n' q : ℤ) : ℂ)) =
        ∑ n ∈ I, ∑ n' ∈ I,
          ((c n * c n' : ℝ) : ℂ) * (κ n * starRingEnd ℂ (κ n')) *
            ((∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_intCast,
      map_intCast, Int.cast_mul]
    ring
  rw [hswap, Complex.re_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun n' hn' => ?_
  set A : ℂ := ((c n * c n' : ℝ) : ℂ) * (κ n * starRingEnd ℂ (κ n')) *
    ((∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ) : ℝ) : ℂ)
  have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n hn) (hc n' hn')
  have hκprod : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
    have h1 : ‖κ n‖ * ‖κ n'‖ ≤ 1 * 1 :=
      mul_le_mul (hκ n hn) (hκ n' hn') (norm_nonneg _) zero_le_one
    linarith
  calc A.re
      ≤ ‖A‖ := Complex.re_le_norm A
    _ = |c n| * |c n'| * (‖κ n‖ * ‖κ n'‖) * |∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ)| := by
        simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    _ = (c n * c n') * (‖κ n‖ * ‖κ n'‖) * |∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ)| := by
        rw [abs_of_nonneg (hc n hn), abs_of_nonneg (hc n' hn')]
    _ ≤ (c n * c n') * 1 * |∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκprod hcc) (abs_nonneg _)
    _ = c n * c n' * |∑ q ∈ P, ((χ n q * χ n' q : ℤ) : ℝ)| := by ring

/-- Exact diagonal / exceptional-conductor / off-diagonal splitting of the mean-square
double sum (`MeanSqAbs.lean` / `meansq_split`). -/
theorem meansq_split {β : Type*} [DecidableEq β] (I : Finset β)
    (c : β → ℝ) (hc : ∀ n ∈ I, 0 ≤ c n)
    (r : β → β → ℕ) (Sval : β → β → ℝ) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 ≤ η) (nstar : ℕ)
    (hS_all : ∀ n ∈ I, ∀ n' ∈ I, Sval n n' ≤ M)
    (hS_off : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → Sval n n' ≤ η * M) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * Sval n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
       (∑ n ∈ I, ∑ n' ∈ I, if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
       η * (∑ n ∈ I, c n) ^ 2) * M := by
  have hpair : ∀ n ∈ I, ∀ n' ∈ I,
      c n * c n' * Sval n n' ≤
        ((if r n n' = 1 then c n * c n' else 0) +
         (if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
         η * (c n * c n')) * M := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n hn) (hc n' hn')
    by_cases h1 : r n n' = 1
    · rw [if_pos h1, if_neg (fun h => h.1 h1), add_zero]
      have h2 := mul_le_mul_of_nonneg_left (hS_all n hn n' hn') hcc
      have h3 : 0 ≤ η * (c n * c n') * M := by positivity
      linarith
    · by_cases h2 : r n n' = nstar
      · rw [if_neg h1, if_pos ⟨h1, h2⟩, zero_add]
        have h3 := mul_le_mul_of_nonneg_left (hS_all n hn n' hn') hcc
        have h4 : 0 ≤ η * (c n * c n') * M := by positivity
        linarith
      · rw [if_neg h1, if_neg (fun h => h2 h.2), zero_add, zero_add]
        have h3 := mul_le_mul_of_nonneg_left (hS_off n hn n' hn' h1 h2) hcc
        linarith
  have hsum :
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * Sval n n' ≤
        ∑ n ∈ I, ∑ n' ∈ I,
          ((if r n n' = 1 then c n * c n' else 0) +
           (if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
           η * (c n * c n')) * M :=
    Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpair n hn n' hn'
  refine hsum.trans ?_
  have hrhs :
      ∑ n ∈ I, ∑ n' ∈ I,
          ((if r n n' = 1 then c n * c n' else 0) +
           (if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
           η * (c n * c n')) * M =
        ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
         (∑ n ∈ I, ∑ n' ∈ I, if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
         η * (∑ n ∈ I, c n) ^ 2) * M := by
    simp_rw [← Finset.sum_mul, Finset.sum_add_distrib]
    congr 1
    congr 1
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hrhs]

/-- Combined Jacobi character mean-square inequality: bounding
`∑_{q ∈ P} ‖∑_{n ∈ I} c(n) κ(n) (n / q)‖²` by diagonal, exceptional-conductor, and
cancellation terms. -/
theorem jacobi_meansq_bound (P I : Finset ℕ)
    (c : ℕ → ℝ) (hc : ∀ n ∈ I, 0 ≤ c n)
    (κ : ℕ → ℂ) (hκ : ∀ n ∈ I, ‖κ n‖ ≤ 1)
    (r : ℕ → ℕ → ℕ) (η : ℝ) (hη : 0 ≤ η) (nstar : ℕ)
    (hJ_off : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar →
      |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| ≤ η * (P.card : ℝ)) :
    ∑ q ∈ P, ‖∑ n ∈ I, (c n : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
       (∑ n ∈ I, ∑ n' ∈ I, if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) +
       η * (∑ n ∈ I, c n) ^ 2) * (P.card : ℝ) := by
  refine (meansq_expand P I c hc κ hκ (fun n q => jacobiSym (n : ℤ) q)).trans ?_
  refine meansq_split I c hc r
    (fun n n' => |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|)
    (P.card : ℝ) η (Nat.cast_nonneg _) hη nstar ?_ hJ_off
  intro n _ n' _
  calc |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|
      ≤ ∑ q ∈ P, |((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ P, (1 : ℝ) := by
        refine Finset.sum_le_sum fun q _ => ?_
        have h1 : |((jacobiSym (n : ℤ) q : ℤ) : ℝ)| ≤ 1 := by
          rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h]
        have h2 : |((jacobiSym (n' : ℤ) q : ℤ) : ℝ)| ≤ 1 := by
          rcases jacobiSym.trichotomy (n' : ℤ) q with h | h | h <;> simp [h]
        rw [Int.cast_mul, abs_mul]
        nlinarith [abs_nonneg ((jacobiSym (n : ℤ) q : ℤ) : ℝ),
          abs_nonneg ((jacobiSym (n' : ℤ) q : ℤ) : ℝ)]
    _ = (P.card : ℝ) := by simp

/-- Markov/Chebyshev extraction of the bad-set cardinality from an `L²` mean-square bound:
if `∑_{q ∈ P} f(q)² ≤ M * |P|` and every `q ∈ B ⊆ P` has `T ≤ |f(q)|` (`T > 0`), then
`|B| ≤ (M / T²) * |P|`. -/
theorem chebyshev_bad_card {α : Type*} [DecidableEq α] {P B : Finset α}
    (hBP : B ⊆ P) (f : α → ℝ) {M T : ℝ} (hT : 0 < T)
    (hMS : ∑ q ∈ P, f q ^ 2 ≤ M * (P.card : ℝ))
    (hBad : ∀ q ∈ B, T ≤ |f q|) :
    (B.card : ℝ) ≤ (M / T ^ 2) * (P.card : ℝ) := by
  have h1 : (B.card : ℝ) * T ^ 2 ≤ ∑ q ∈ B, f q ^ 2 := by
    calc (B.card : ℝ) * T ^ 2
        = ∑ _q ∈ B, T ^ 2 := by simp
      _ ≤ ∑ q ∈ B, f q ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [← sq_abs (f q)]
          exact pow_le_pow_left₀ hT.le (hBad q hq) 2
  have h2 : ∑ q ∈ B, f q ^ 2 ≤ ∑ q ∈ P, f q ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBP (fun _ _ _ => sq_nonneg _)
  have h3 : (B.card : ℝ) * T ^ 2 ≤ M * (P.card : ℝ) := h1.trans (h2.trans hMS)
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hT)]
  exact h3

/-- Complement extraction (`PairShare.lean` / `share_of_bad`): if every bad subset `B ⊆ P`
has `|B| ≤ η * |P|`, then the good subset `G ⊆ P` satisfies `(1 - η) * |P| ≤ |G|`. -/
theorem share_of_bad {α : Type*} (P : Finset α) {η : ℝ} (p : α → Prop)
    (h : ∀ B ⊆ P, (∀ q ∈ B, ¬ p q) → (B.card : ℝ) ≤ η * (P.card : ℝ)) :
    ∃ G ⊆ P, (1 - η) * (P.card : ℝ) ≤ (G.card : ℝ) ∧ ∀ q ∈ G, p q := by
  classical
  refine ⟨P.filter p, Finset.filter_subset _ _, ?_, fun q hq => (Finset.mem_filter.1 hq).2⟩
  have h1 := h (P.filter fun q => ¬ p q) (Finset.filter_subset _ _)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  have h2 : ((P.filter p).card : ℝ) + ((P.filter fun q => ¬ p q).card : ℝ) = (P.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := P) p
  linarith

/-- Zero-free box `Re(s) > 1 - 1/400`, `|Im(s)| ≤ Q` for a Dirichlet character `ψ`. -/
def ZeroFreeBox (Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction ψ s ≠ 0

/-- Abstract zero-density box count hypothesis: any finite family of primitive characters
of conductor `≤ Q` failing `ZeroFreeBox Q` has cardinality `≤ C * Q ^ (1 / 4)`. -/
def ZeroDensityBoxBound (C : ℝ) : Prop :=
  ∀ (Q : ℝ) (F : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))), 3 ≤ Q →
    (∀ p ∈ F, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (F.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

private theorem sigma_of_not_zeroFreeBox (Q : ℝ) (M : ℕ) [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hp : ψ.IsPrimitive) (hM : (M : ℝ) ≤ Q)
    (hz : ¬ ZeroFreeBox Q ψ) :
    ∃ p : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)),
      p.1 + 1 = M ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  refine ⟨⟨k, ψ⟩, rfl, hp, hM, ?_⟩
  unfold ZeroFreeBox at hz
  push Not at hz
  exact hz

/-- Bad-prime counting from a zero-density box bound (`CountBadCore.lean` / `CountBad.lean`):
primes `q > F` dividing the conductor `f * q ≤ Q` (`f ≤ F`) of a primitive character failing
`ZeroFreeBox Q` inject into the bad characters, giving `|S| ≤ max C 0 * Q ^ (1 / 4)`. -/
theorem count_bad_of_zeroDensityBox {C : ℝ} (hZD : ZeroDensityBoxBound C)
    (Q F : ℝ) (S : Finset ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ q ∈ S, q.Prime ∧ F < (q : ℝ) ∧
      ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) :
    (S.card : ℝ) ≤ max C 0 * Q ^ (1 / 4 : ℝ) := by
  classical
  have key : ∀ q : ℕ, ∃ p : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)), q ∈ S →
      (∃ f : ℕ, p.1 + 1 = f * q ∧ (f : ℝ) ≤ F) ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨-, -, f, hne, ψ, hf, hNQ, hp, hz⟩ := hS q hq
      obtain ⟨p, h1, h2⟩ := sigma_of_not_zeroFreeBox Q (f * q) ψ hp hNQ hz
      exact ⟨p, fun _ => ⟨⟨f, h1, hf⟩, h2⟩⟩
    · exact ⟨⟨0, 1⟩, fun h => absurd h hq⟩
  choose g hg using key
  have hinj : Set.InjOn g S := by
    intro q hq q' hq' h
    obtain ⟨⟨f, hf, -⟩, -⟩ := hg q hq
    obtain ⟨⟨f', hf', hF'⟩, -⟩ := hg q' hq'
    have hpq := (hS q hq).1
    have hpq' := (hS q' hq').1
    have hlt := (hS q hq).2.1
    have he : f * q = f' * q' := by rw [← hf, ← hf', h]
    have hd : q ∣ f' * q' := ⟨f, by rw [← he, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hpq).1 hd with h1 | h1
    · have hpos : 0 < f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0] at hf'; simp at hf'
        · exact h0
      have : (q : ℝ) ≤ f' := by exact_mod_cast Nat.le_of_dvd hpos h1
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hpq hpq').1 h1
  have h1 := hZD Q (S.image g) hQ (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (hg q hq).2)
  rw [Finset.card_image_of_injOn hinj] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact Real.rpow_nonneg (by linarith) _

/-- Two-stage prime-pair good-share extraction (`PairShare.lean`): combining first-stage
and second-stage bad-prime bounds yields dense good prime pairs `(q, d)` with share `≥ 1 - η`. -/
theorem pair_share_of_stages {α β : Type*} (P₁ : Finset α) (P₂ : α → Finset β)
    {η : ℝ} (Good₁ : α → Prop) (Good₂ : α → β → Prop)
    (h1 : P₁.Nonempty ∧ ∀ B ⊆ P₁, (∀ q ∈ B, ¬ Good₁ q) → (B.card : ℝ) ≤ η * (P₁.card : ℝ))
    (h2 : ∀ q ∈ P₁, (P₂ q).Nonempty ∧
      ∀ B ⊆ P₂ q, (∀ d ∈ B, ¬ Good₂ q d) → (B.card : ℝ) ≤ η * ((P₂ q).card : ℝ)) :
    ∃ G₁ ⊆ P₁, 0 < P₁.card ∧ (1 - η) * (P₁.card : ℝ) ≤ (G₁.card : ℝ) ∧
      ∀ q ∈ G₁, Good₁ q ∧
        ∃ G₂ ⊆ P₂ q, 0 < (P₂ q).card ∧ (1 - η) * ((P₂ q).card : ℝ) ≤ (G₂.card : ℝ) ∧
          ∀ d ∈ G₂, Good₂ q d := by
  obtain ⟨hne1, hb1⟩ := h1
  obtain ⟨G₁, hG₁s, hG₁c, hG₁⟩ := share_of_bad P₁ Good₁ hb1
  refine ⟨G₁, hG₁s, hne1.card_pos, hG₁c, fun q hq => ⟨hG₁ q hq, ?_⟩⟩
  obtain ⟨hne2, hb2⟩ := h2 q (hG₁s hq)
  obtain ⟨G₂, hG₂s, hG₂c, hG₂⟩ := share_of_bad (P₂ q) (Good₂ q) hb2
  exact ⟨G₂, hG₂s, hne2.card_pos, hG₂c, hG₂⟩

/-! ## 4. Explicit Formula Error Bracket & Window-Coupling Calculus (`SChain`, `GrowthBracketBound`) -/

/-- Exact `δ₁(x, ε) = x ^ (-(ε / 8))` density loss factor from `GrowthBracketBoundOfSizeWindows`. -/
def delta1 (x ε : ℝ) : ℝ := x ^ (-(ε / 8))

/-- Exact normalized error bracket `bracketSizeWindowBrackets` from
`Formalism/SizeWindowBrackets/GrowthBracketBoundOfSizeWindows.lean`. -/
def bracketSizeWindowBrackets (c C ε x : ℝ) (n nT2 m : ℕ) (k : ℝ) : ℝ :=
  x ^ (C * ε) *
    (c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
      2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2)) +
  2 * x ^ ((1 : ℝ) / 2 + ε) + 2 / x

/-- Exact algebraic rewriting of the `Nc` term in `errorBracketSizeWindows` (`NcForm`). -/
theorem nc_term_eq {ε x b k : ℝ} {n nT2 : ℕ} (hx : 0 < x) (hn : 0 < n) :
    (nT2 : ℝ) * k * b * x ^ ε / ((n : ℝ) * ((n : ℝ) * x ^ (-ε))) =
      ((nT2 : ℝ) / (n : ℝ)) * k * b * x ^ (2 * ε) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxe : x ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos hx (-ε)).ne'
  have h2e : x ^ (2 * ε) = x ^ ε / x ^ (-ε) := by
    rw [Real.rpow_neg hx.le, div_inv_eq_mul, ← Real.rpow_add hx]
    ring_nf
  rw [h2e]
  field_simp [hn', hxe]

/-- Dividing `errorBracketSizeWindows` (from `RHDirect.Interfaces`) by `(nT : ℝ) * m * b`
under `RestSize` and `aE ≤ c * x * b`. -/
theorem errorBracket_div_scale_le {c ε x : ℝ} {n nT nT2 m : ℕ} {b k aE : ℝ}
    (hx : 0 < x) (hn : 0 < n) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (haEc : aE ≤ c * x * b) (hRest : RestSize ε x n nT nT2 m b k aE) :
    errorBracketSizeWindows x ε n nT nT2 m b k aE / ((nT : ℝ) * (m : ℝ) * b) ≤
      c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
        2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) := by
  obtain ⟨-, hnT_lo, -, -, -⟩ := hRest
  have hd1 : 0 < delta1 x ε := Real.rpow_pos_of_pos hx _
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnT_pos : (0 : ℝ) < (nT : ℝ) := lt_of_lt_of_le (by unfold delta1 at hd1; positivity) hnT_lo
  have hratio : (n : ℝ) / (nT : ℝ) ≤ 2 / delta1 x ε := by
    rw [div_le_div_iff₀ hnT_pos hd1]
    unfold delta1
    linarith
  have hterm1 :
      (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k) / ((nT : ℝ) * (m : ℝ) * b) ≤
        c * x / (m : ℝ) + c * x * (m : ℝ) / k := by
    have hEq : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k) / ((nT : ℝ) * (m : ℝ) * b) =
        (aE / b) * (1 / (m : ℝ) + (m : ℝ) / k) := by
      field_simp [hnT_pos.ne', hm'.ne', hb.ne', hk.ne']
    rw [hEq]
    have hab : aE / b ≤ c * x := (div_le_iff₀ hb).mpr haEc
    have hfac : 0 ≤ 1 / (m : ℝ) + (m : ℝ) / k := by positivity
    calc (aE / b) * (1 / (m : ℝ) + (m : ℝ) / k)
        ≤ (c * x) * (1 / (m : ℝ) + (m : ℝ) / k) := mul_le_mul_of_nonneg_right hab hfac
      _ = c * x / (m : ℝ) + c * x * (m : ℝ) / k := by ring
  have hterm2 :
      (m : ℝ) * (2 * (n : ℝ) * (m : ℝ) * b * x ^ ε) / ((nT : ℝ) * (m : ℝ) * b) ≤
        4 * (m : ℝ) * x ^ ε / delta1 x ε := by
    have hEq : (m : ℝ) * (2 * (n : ℝ) * (m : ℝ) * b * x ^ ε) / ((nT : ℝ) * (m : ℝ) * b) =
        ((n : ℝ) / (nT : ℝ)) * (2 * (m : ℝ) * x ^ ε) := by
      field_simp [hnT_pos.ne', hm'.ne', hb.ne']
    rw [hEq]
    calc ((n : ℝ) / (nT : ℝ)) * (2 * (m : ℝ) * x ^ ε)
        ≤ (2 / delta1 x ε) * (2 * (m : ℝ) * x ^ ε) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = 4 * (m : ℝ) * x ^ ε / delta1 x ε := by ring
  have hterm3 :
      (m : ℝ) * ((nT2 : ℝ) * k * b * x ^ ε / ((n : ℝ) * ((n : ℝ) * x ^ (-ε)))) /
          ((nT : ℝ) * (m : ℝ) * b) ≤
        2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) := by
    rw [nc_term_eq hx hn]
    have hEq :
        (m : ℝ) * (((nT2 : ℝ) / (n : ℝ)) * k * b * x ^ (2 * ε) / (n : ℝ)) /
            ((nT : ℝ) * (m : ℝ) * b) =
          ((n : ℝ) / (nT : ℝ)) * (k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (n : ℝ) ^ 2) := by
      field_simp [hnT_pos.ne', hm'.ne', hb.ne', hn'.ne']
    rw [hEq]
    calc ((n : ℝ) / (nT : ℝ)) * (k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (n : ℝ) ^ 2)
        ≤ (2 / delta1 x ε) * (k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = 2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) := by
          field_simp [hd1.ne', hn'.ne']
  unfold errorBracketSizeWindows
  rw [add_div, mul_add (m : ℝ), add_div]
  linarith

/-- Reduction of the main explicit-formula / slope inequality to `bracketSizeWindowBrackets`
(`GrowthBracketBoundOfSizeWindows` for both `c = 1` and `c = 2`). -/
theorem growth_le_bracketSizeWindowBrackets {c C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE Err Gx : ℝ}
    (hx : 0 < x) (hn : 0 < n) (hnT2 : nT2 ≤ n) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (haEc : aE ≤ c * x * b)
    (hRest : RestSize ε x n nT nT2 m b k aE)
    (hErr : Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE)
    (hMain : (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) *
        (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * (m : ℝ) * b / x) :
    ((nT2 : ℝ) / (n : ℝ)) / 2 * Gx ≤ bracketSizeWindowBrackets c C ε x n nT2 m k := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hd1 : 0 < delta1 x ε := Real.rpow_pos_of_pos hx _
  have hnT_pos : (0 : ℝ) < (nT : ℝ) :=
    lt_of_lt_of_le (by unfold delta1 at hd1; positivity) hRest.2.1
  have hS_pos : 0 < (nT : ℝ) * (m : ℝ) * b := by positivity
  have hdiv :
      (((nT2 : ℝ) / (n : ℝ)) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
        Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x := by
    have h1 := div_le_div_of_nonneg_right hMain hS_pos.le
    have hL :
        (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) /
            ((nT : ℝ) * (m : ℝ) * b) =
          (((nT2 : ℝ) / (n : ℝ)) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) := by
      field_simp [hS_pos.ne']
    have hR : (Err + 2 * (nT : ℝ) * (m : ℝ) * b / x) / ((nT : ℝ) * (m : ℝ) * b) =
        Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x := by
      field_simp [hS_pos.ne', hx.ne']
    linarith
  have hErrDiv :
      Err / ((nT : ℝ) * (m : ℝ) * b) ≤
        x ^ (C * ε) *
          (c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
            2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2)) := by
    calc Err / ((nT : ℝ) * (m : ℝ) * b)
        ≤ (x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE) /
            ((nT : ℝ) * (m : ℝ) * b) := div_le_div_of_nonneg_right hErr hS_pos.le
      _ = x ^ (C * ε) *
            (errorBracketSizeWindows x ε n nT nT2 m b k aE / ((nT : ℝ) * (m : ℝ) * b)) := by
          ring
      _ ≤ x ^ (C * ε) *
            (c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
              2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (errorBracket_div_scale_le hx hn hm hb hk haEc hRest)
            (Real.rpow_nonneg hx.le _)
  have hratio_le : (nT2 : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hnT2
  have hshift :
      (((nT2 : ℝ) / (n : ℝ)) / 2) * (4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ 2 * x ^ ((1 : ℝ) / 2 + ε) := by
    have hxpow : 0 ≤ x ^ ((1 : ℝ) / 2 + ε) := Real.rpow_nonneg hx.le _
    nlinarith
  unfold bracketSizeWindowBrackets
  linarith

/-- Sharp bracket size bound for tight `m ∈ [x^(1/2 - ε/8), x^(1/2)]`
(`BracketSizes` in `GrowthBracketBoundOfSizeWindows.lean`, generalized to arbitrary `c ≥ 0`). -/
theorem bracketSizes_tight {c C ε x : ℝ} {n nT2 m : ℕ} {k : ℝ}
    (hc : 0 ≤ c) (hx : 1 ≤ x) (hε : 0 < ε) (hn : 0 < n) (hnT2 : nT2 ≤ n)
    (hm_lo : x ^ ((1 : ℝ) / 2 - ε / 8) ≤ (m : ℝ)) (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2))
    (hk_lo : x * (m : ℝ) ≤ k) (hk_hi : k ≤ x ^ ((1 : ℝ) / 2 - ε) * (n : ℝ) ^ 2) :
    bracketSizeWindowBrackets c C ε x n nT2 m k ≤
      (2 * c + 6) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) + 2 * x ^ ((1 : ℝ) / 2 + ε) + 2 / x := by
  have hx0 : 0 < x := by linarith
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm_lo
  have hk0 : 0 < k := lt_of_lt_of_le (mul_pos hx0 hm0) hk_lo
  have hd1 : 0 < delta1 x ε := Real.rpow_pos_of_pos hx0 _
  have h1 : c * x / (m : ℝ) ≤ c * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
    calc c * x / (m : ℝ)
        ≤ c * x / x ^ ((1 : ℝ) / 2 - ε / 8) := by
          gcongr
      _ = c * (x ^ (1 : ℝ) / x ^ ((1 : ℝ) / 2 - ε / 8)) := by
          rw [mul_div_assoc, Real.rpow_one]
      _ = c * x ^ ((1 : ℝ) / 2 + ε / 8) := by
          rw [← Real.rpow_sub hx0]
          ring_nf
      _ ≤ c * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hc
  have h2 : c * x * (m : ℝ) / k ≤ c * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
    have hxm : x * (m : ℝ) / k ≤ 1 := (div_le_one hk0).mpr hk_lo
    have hpow : 1 ≤ x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := Real.one_le_rpow hx (by linarith)
    calc c * x * (m : ℝ) / k
        = c * (x * (m : ℝ) / k) := by ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hxm hc
      _ ≤ c * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := mul_le_mul_of_nonneg_left hpow hc
  have h3 : 4 * (m : ℝ) * x ^ ε / delta1 x ε ≤ 4 * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
    unfold delta1
    rw [Real.rpow_neg hx0.le, div_inv_eq_mul]
    calc 4 * (m : ℝ) * x ^ ε * x ^ (ε / 8)
        ≤ 4 * x ^ ((1 : ℝ) / 2) * x ^ ε * x ^ (ε / 8) := by gcongr
      _ = 4 * (x ^ ((1 : ℝ) / 2) * x ^ ε * x ^ (ε / 8)) := by ring
      _ = 4 * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          ring_nf
  have h4 :
      2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) ≤
        2 * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
    have hrat : (nT2 : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast hnT2)
    have hkn : k / (n : ℝ) ^ 2 ≤ x ^ ((1 : ℝ) / 2 - ε) :=
      (div_le_iff₀ (sq_pos_of_pos hn')).mpr hk_hi
    have hEq :
        2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) =
          2 * (k / (n : ℝ) ^ 2) * ((nT2 : ℝ) / (n : ℝ)) * (x ^ (2 * ε) / delta1 x ε) := by
      field_simp [hd1.ne', hn'.ne']
    rw [hEq]
    have hxe : x ^ (2 * ε) / delta1 x ε = x ^ (17 / 8 * ε) := by
      unfold delta1
      rw [Real.rpow_neg hx0.le, div_inv_eq_mul, ← Real.rpow_add hx0]
      ring_nf
    rw [hxe]
    calc 2 * (k / (n : ℝ) ^ 2) * ((nT2 : ℝ) / (n : ℝ)) * x ^ (17 / 8 * ε)
        ≤ 2 * x ^ ((1 : ℝ) / 2 - ε) * 1 * x ^ (17 / 8 * ε) := by gcongr
      _ = 2 * (x ^ ((1 : ℝ) / 2 - ε) * x ^ (17 / 8 * ε)) := by ring
      _ = 2 * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
  unfold bracketSizeWindowBrackets
  have hsum :
      c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
          2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) ≤
        (2 * c + 6) * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
    linarith
  have hmul :
      x ^ (C * ε) *
          (c * x / (m : ℝ) + c * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
            2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2)) ≤
        (2 * c + 6) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) := by
    calc x ^ (C * ε) * _
        ≤ x ^ (C * ε) * ((2 * c + 6) * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε)) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hx0.le _)
      _ = (2 * c + 6) * (x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε)) := by ring
      _ = (2 * c + 6) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
  linarith

/-- Sharp conclusion (`BracketConclusion`) for tight `m ∈ [x^(1/2 - ε/8), x^(1/2)]`:
if `4 * c + 20 ≤ x ^ (7 * ε / 8)` (i.e. `24 ≤ x ^ (7 * ε / 8)` at `c = 1`, `28 ≤ x ^ (7 * ε / 8)`
at `c = 2`), then `Gx ≤ x ^ (1 / 2 + (C + 3) * ε)`. -/
theorem bracketConclusion_tight {c C ε x : ℝ} {n nT2 m : ℕ} {k Gx : ℝ}
    (hc : 0 ≤ c) (hx : 1 ≤ x) (hε : 0 < ε) (hC : 0 ≤ C) (hn : 0 < n) (hnT2 : nT2 ≤ n)
    (hT2_lo : x ^ (-ε) ≤ (nT2 : ℝ) / (n : ℝ))
    (hm_lo : x ^ ((1 : ℝ) / 2 - ε / 8) ≤ (m : ℝ)) (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2))
    (hk_lo : x * (m : ℝ) ≤ k) (hk_hi : k ≤ x ^ ((1 : ℝ) / 2 - ε) * (n : ℝ) ^ 2)
    (hX : 4 * c + 20 ≤ x ^ (7 * ε / 8))
    (hB : ((nT2 : ℝ) / (n : ℝ)) / 2 * Gx ≤ bracketSizeWindowBrackets c C ε x n nT2 m k) :
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
  have hx0 : 0 < x := by linarith
  have h1 := hB.trans (bracketSizes_tight hc hx hε hn hnT2 hm_lo hm_hi hk_lo hk_hi)
  have h2 : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have h3 : 2 / x ≤ 2 * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) := by
    have hdiv : 2 / x ≤ 2 := by
      rw [div_le_iff₀ hx0]
      linarith
    have hge1 : 1 ≤ x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) :=
      Real.one_le_rpow hx (by nlinarith)
    linarith
  have htot : ((nT2 : ℝ) / (n : ℝ)) / 2 * Gx ≤
      (2 * c + 10) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) := by
    linarith
  have hden : 0 < x ^ (-ε) / 2 := by positivity
  have hden_le : x ^ (-ε) / 2 ≤ ((nT2 : ℝ) / (n : ℝ)) / 2 := by linarith
  by_cases hG : Gx ≤ 0
  · exact hG.trans (Real.rpow_nonneg hx0.le _)
  · push Not at hG
    have hstep : x ^ (-ε) / 2 * Gx ≤ (2 * c + 10) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) :=
      le_trans (mul_le_mul_of_nonneg_right hden_le hG.le) htot
    have hmul := mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ 2 * x ^ ε by positivity)
    have hL : 2 * x ^ ε * (x ^ (-ε) / 2 * Gx) = Gx := by
      have hinv : x ^ ε * x ^ (-ε) = 1 := by
        rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
      calc 2 * x ^ ε * (x ^ (-ε) / 2 * Gx)
          = (x ^ ε * x ^ (-ε)) * Gx := by ring
        _ = Gx := by rw [hinv, one_mul]
    rw [hL] at hmul
    calc Gx
        ≤ 2 * x ^ ε * ((2 * c + 10) * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε)) := hmul
      _ = (4 * c + 20) * (x ^ ε * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε)) := by ring
      _ = (4 * c + 20) * x ^ ((1 : ℝ) / 2 + (C + 17 / 8) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
      _ ≤ x ^ (7 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 17 / 8) * ε) :=
          mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf

/-- Full `RestSize` (`SChain.lean`) window bracket bound: allowing the wider chain-length
envelope `x ^ (1/2 - ε) ≤ m ≤ x ^ (1/2 + ε/2)` and `aE ≤ 2 * x * b` with `3 ≤ x` and
`26 ≤ x ^ (3 * ε / 8)` directly implies `Gx ≤ x ^ (1 / 2 + (C + 3) * ε)`! -/
theorem growth_bound_of_restSize {C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE Err Gx : ℝ}
    (hx : 3 ≤ x) (hε : 0 < ε) (hC : 0 ≤ C) (hn : 0 < n) (hnT2 : nT2 ≤ n)
    (hb : 0 < b)
    (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hk_lo : x * (m : ℝ) ≤ k)
    (hX : 26 ≤ x ^ (3 * ε / 8))
    (hRest : RestSize ε x n nT nT2 m b k aE)
    (hErr : Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE)
    (hMain : (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) *
        (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * (m : ℝ) * b / x) :
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have haE2 : aE ≤ 2 * x * b := hRest.1
  have hT2_lo : x ^ (-ε) ≤ (nT2 : ℝ) / (n : ℝ) := hRest.2.2.1
  have hm_lo : x ^ ((1 : ℝ) / 2 - ε) ≤ (m : ℝ) := hRest.2.2.2.1
  have hk_hi : k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := hRest.2.2.2.2
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm_lo
  have hm_nat : 0 < m := Nat.cast_pos.mp hm0
  have hk0 : 0 < k := lt_of_lt_of_le (mul_pos hx0 hm0) hk_lo
  have hd1 : 0 < delta1 x ε := Real.rpow_pos_of_pos hx0 _
  have hB := growth_le_bracketSizeWindowBrackets (c := 2) hx0 hn hnT2 hm_nat hb hk0 haE2
    hRest hErr hMain
  have h1 : 2 * x / (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by
    calc 2 * x / (m : ℝ)
        ≤ 2 * x / x ^ ((1 : ℝ) / 2 - ε) := by gcongr
      _ = 2 * (x ^ (1 : ℝ) / x ^ ((1 : ℝ) / 2 - ε)) := by
          rw [mul_div_assoc, Real.rpow_one]
      _ = 2 * x ^ ((1 : ℝ) / 2 + ε) := by
          rw [← Real.rpow_sub hx0]
          ring_nf
      _ ≤ 2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
            (by norm_num)
  have h2 : 2 * x * (m : ℝ) / k ≤ 2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by
    have hxm : x * (m : ℝ) / k ≤ 1 := (div_le_one hk0).mpr hk_lo
    have hpow : 1 ≤ x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := Real.one_le_rpow hx1 (by linarith)
    calc 2 * x * (m : ℝ) / k
        = 2 * (x * (m : ℝ) / k) := by ring
      _ ≤ 2 * 1 := by linarith
      _ ≤ 2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by linarith
  have h3 : 4 * (m : ℝ) * x ^ ε / delta1 x ε ≤ 4 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by
    unfold delta1
    rw [Real.rpow_neg hx0.le, div_inv_eq_mul]
    calc 4 * (m : ℝ) * x ^ ε * x ^ (ε / 8)
        ≤ 4 * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) := by gcongr
      _ = 4 * (x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8)) := by ring
      _ = 4 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          ring_nf
  have h4 :
      2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) ≤
        2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) := by
    have hrat : (nT2 : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast hnT2)
    have hkn : k / (n : ℝ) ^ 2 ≤ x ^ ((1 : ℝ) / 2 - ε) := by
      rw [div_le_iff₀ (sq_pos_of_pos hn')]
      linarith
    have hEq :
        2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2) =
          2 * (k / (n : ℝ) ^ 2) * ((nT2 : ℝ) / (n : ℝ)) * (x ^ (2 * ε) / delta1 x ε) := by
      field_simp [hd1.ne', hn'.ne']
    rw [hEq]
    have hxe : x ^ (2 * ε) / delta1 x ε = x ^ (17 / 8 * ε) := by
      unfold delta1
      rw [Real.rpow_neg hx0.le, div_inv_eq_mul, ← Real.rpow_add hx0]
      ring_nf
    rw [hxe]
    calc 2 * (k / (n : ℝ) ^ 2) * ((nT2 : ℝ) / (n : ℝ)) * x ^ (17 / 8 * ε)
        ≤ 2 * x ^ ((1 : ℝ) / 2 - ε) * 1 * x ^ (17 / 8 * ε) := by gcongr
      _ = 2 * (x ^ ((1 : ℝ) / 2 - ε) * x ^ (17 / 8 * ε)) := by ring
      _ = 2 * x ^ ((1 : ℝ) / 2 + 9 / 8 * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
      _ ≤ 2 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
            (by norm_num)
  have hpar :
      x ^ (C * ε) *
          (2 * x / (m : ℝ) + 2 * x * (m : ℝ) / k + 4 * (m : ℝ) * x ^ ε / delta1 x ε +
            2 * k * ((nT2 : ℝ) / (n : ℝ)) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2)) ≤
        10 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
    calc x ^ (C * ε) * _
        ≤ x ^ (C * ε) * (10 * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
      _ = 10 * (x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 / 8 * ε)) := by ring
      _ = 10 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
  have hpow2 : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have htail : 2 / x ≤ 1 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
    have hdiv : 2 / x ≤ 1 := by
      rw [div_le_one hx0]
      linarith
    have hge1 : 1 ≤ x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) :=
      Real.one_le_rpow hx1 (by nlinarith)
    linarith
  have htot :
      ((nT2 : ℝ) / (n : ℝ)) / 2 * Gx ≤ 13 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
    unfold bracketSizeWindowBrackets at hB
    linarith
  by_cases hG : Gx ≤ 0
  · exact hG.trans (Real.rpow_nonneg hx0.le _)
  · push Not at hG
    have hden_le : x ^ (-ε) / 2 ≤ ((nT2 : ℝ) / (n : ℝ)) / 2 := by linarith
    have hstep : x ^ (-ε) / 2 * Gx ≤ 13 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) :=
      le_trans (mul_le_mul_of_nonneg_right hden_le hG.le) htot
    have hmul := mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ 2 * x ^ ε by positivity)
    have hL : 2 * x ^ ε * (x ^ (-ε) / 2 * Gx) = Gx := by
      have hinv : x ^ ε * x ^ (-ε) = 1 := by
        rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
      calc 2 * x ^ ε * (x ^ (-ε) / 2 * Gx)
          = (x ^ ε * x ^ (-ε)) * Gx := by ring
        _ = Gx := by rw [hinv, one_mul]
    rw [hL] at hmul
    calc Gx
        ≤ 2 * x ^ ε * (13 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε)) := hmul
      _ = 26 * (x ^ ε * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε)) := by ring
      _ = 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf
      _ ≤ x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) :=
          mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
          rw [← Real.rpow_add hx0]
          ring_nf

/-- Explicit-formula log-derivative transfer (`ExplicitFormulaErrorOfHostConditions.lean`):
if `1 < X`, `1 ≤ J`, and `X ^ (1 / J) ≤ x`, then `C * log X ≤ (C * J) * log x`. -/
theorem explicitFormula_logDeriv_transfer {C X x J v : ℝ}
    (hC : 0 ≤ C) (hX : 1 < X) (hJ : 1 ≤ J) (hx : X ^ (1 / J) ≤ x)
    (hv : v ≤ C * Real.log X) :
    v ≤ (C * J) * Real.log x := by
  have hX0 : 0 < X := by linarith
  have hJ0 : 0 < J := by linarith
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx
  rw [Real.log_rpow hX0, one_div_mul_eq_div, div_le_iff₀ hJ0] at hlog
  calc v ≤ C * Real.log X := hv
    _ ≤ C * (Real.log x * J) := mul_le_mul_of_nonneg_left hlog hC
    _ = (C * J) * Real.log x := by ring

/-! ## 5. Quantitative Window-Coupling Bridge (`TopPlug` / `TopShape` → `AllLevelsWindowBound (3/2)`) -/

/-- Pointwise explicit-formula / slope-bracket realization data for a level `L` at scale `x`
with error exponent `C ≥ 0` and slack `ε > 0`. -/
structure LevelBracketData (L : Level) (C ε x : ℝ) where
  n : ℕ
  nT : ℕ
  nT2 : ℕ
  m : ℕ
  b : ℝ
  k : ℝ
  aE : ℝ
  Err : ℝ
  n_pos : 0 < n
  nT2_le : nT2 ≤ n
  b_pos : 0 < b
  aE_nonneg : 0 ≤ aE
  m_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)
  k_lo : x * (m : ℝ) ≤ k
  rest : RestSize ε x n nT nT2 m b k aE
  err_le : Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE
  main_le : (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) *
    (L.Gm x - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * (m : ℝ) * b / x

/-- Prop-valued existence of a pointwise explicit-formula / slope-bracket realization
at scale `x` for level `L`. -/
def LevelBracketPoint (L : Level) (C ε x : ℝ) : Prop :=
  Nonempty (LevelBracketData L C ε x)

/-- Pointwise extraction of `L.Gm x ≤ x ^ (1/2 + (C + 3) * ε)` from a `LevelBracketPoint`. -/
theorem level_gm_le_of_bracketPoint {L : Level} {C ε x : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hx : 3 ≤ x) (hX : 26 ≤ x ^ (3 * ε / 8))
    (hP : LevelBracketPoint L C ε x) :
    L.Gm x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
  hP.elim fun P =>
    growth_bound_of_restSize hx hε hC P.n_pos P.nT2_le P.b_pos
      P.m_hi P.k_lo hX P.rest P.err_le P.main_le

/-- Windowed bracket hypothesis for a level `L` at exponent `la`:
there is a uniform error exponent `C ≥ 0` (e.g. `C = cTop7 eD eL = 3`) such that for every
`0 < ε < 1 / 52`, arbitrarily large multiplicative windows `[Y, Y ^ la]` carry a
`LevelBracketPoint L C ε y` at every point `y ∈ [Y, Y ^ la]`. -/
def LevelBracketWindows (L : Level) (la : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      HasWindows {y : ℝ | LevelBracketPoint L C ε y} la

/-- Core quantitative window-coupling bridge:
`LevelBracketWindows L la` (with `ε < 1 / 52`) directly implies `LevelWindowBound L la`! -/
theorem levelWindowBound_of_bracketWindows {L : Level} {la : ℝ}
    (hW : LevelBracketWindows L la) :
    LevelWindowBound L la := by
  obtain ⟨C, hC, hWin⟩ := hW
  intro θ hθ _hθ1 Y₀
  obtain ⟨ε, hε0, hε52, -, hθ_gt⟩ := exists_eps_lt_one_div_52_for_theta hθ hC
  let Y₁ : ℝ := max (max Y₀ 3) ((26 : ℝ) ^ (8 / (3 * ε)))
  obtain ⟨Y, hY_ge, hsub⟩ := hWin ε hε0 hε52 Y₁
  have hY₀ : Y₀ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY_ge
  have hY3 : 3 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY_ge
  have hY26 : (26 : ℝ) ^ (8 / (3 * ε)) ≤ Y := le_trans (le_max_right _ _) hY_ge
  refine ⟨Y, hY₀, fun y hy => ?_⟩
  have h1la : 1 + (la - 1) = la := by ring
  rw [h1la] at hy
  have hy3 : 3 ≤ y := le_trans hY3 hy.1
  have hy1 : 1 ≤ y := by linarith
  have h26y : 26 ≤ y ^ (3 * ε / 8) := by
    have hpow := Real.rpow_le_rpow (by positivity) (le_trans hY26 hy.1)
      (show (0 : ℝ) ≤ 3 * ε / 8 by positivity)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 26)] at hpow
    have hmul : 8 / (3 * ε) * (3 * ε / 8) = 1 := by field_simp [hε0.ne']
    rw [hmul, Real.rpow_one] at hpow
    exact hpow
  have hGm : L.Gm y ≤ y ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
    level_gm_le_of_bracketPoint hC hε0 hy3 h26y (hsub hy)
  rw [one_mul]
  exact hGm.trans (Real.rpow_le_rpow_of_exponent_le hy1 hθ_gt.le)

/-- Restricting square `[Y, Y^2]` bracket windows (delivered by `VWinAt`) to the
`la = 3/2` windows `[Y, Y^(3/2)]` yields `LevelWindowBound L (3 / 2)`. -/
theorem levelWindowBound_three_halves_of_square_brackets {L : Level}
    (hW : LevelBracketWindows L 2) :
    LevelWindowBound L (3 / 2) := by
  apply levelWindowBound_of_bracketWindows
  obtain ⟨C, hC, hWin⟩ := hW
  refine ⟨C, hC, fun ε hε0 hε52 Y₀ => ?_⟩
  obtain ⟨Y, hY, hsub⟩ := hWin ε hε0 hε52 (max Y₀ 1)
  exact ⟨Y, le_trans (le_max_left _ _) hY,
    (Icc_three_halves_subset_square (le_trans (le_max_right _ _) hY)).trans hsub⟩

/-- Direct conversion of pointwise growth windows on `[Y, Y^2]` (at `0 < ε < 1/52` with
joint exponent `cTop7 eD eL`) into `LevelWindowBound L (3 / 2)`. -/
theorem levelWindowBound_three_halves_of_growth_windows {L : Level} {eD eL : ℝ}
    (hW : ∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      HasWindows {y : ℝ | L.Gm y ≤ y ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)} 2) :
    LevelWindowBound L (3 / 2) := by
  have hC : 0 ≤ cTop7 eD eL := le_trans (by norm_num) (three_le_cTop7 eD eL)
  intro θ hθ _hθ1 Y₀
  obtain ⟨ε, hε0, hε52, -, hθ_gt⟩ := exists_eps_lt_one_div_52_for_theta hθ hC
  obtain ⟨Y, hY, hsub⟩ := hW ε hε0 hε52 (max Y₀ 1)
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  refine ⟨Y, le_trans (le_max_left _ _) hY, fun y hy => ?_⟩
  have h1la : (1 : ℝ) + ((3 / 2 : ℝ) - 1) = 3 / 2 := by norm_num
  rw [h1la] at hy
  have hy2 : y ∈ Set.Icc Y (Y ^ (2 : ℝ)) := Icc_three_halves_subset_square hY1 hy
  have hGm : L.Gm y ≤ y ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε) := hsub hy2
  rw [one_mul]
  exact hGm.trans (Real.rpow_le_rpow_of_exponent_le (le_trans hY1 hy.1) hθ_gt.le)

/-- `AllLevelsWindowBound (3 / 2)` from cyclic bracket windows at `la = 3 / 2`. -/
theorem allLevelsWindowBound_three_halves_of_brackets
    (hAll : ∀ ψ : PChar, LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    AllLevelsWindowBound (3 / 2) :=
  fun ψ => levelWindowBound_of_bracketWindows (hAll ψ)

/-- `AllLevelsWindowBound (3 / 2)` from cyclic square bracket windows (`[Y, Y^2]`). -/
theorem allLevelsWindowBound_three_halves_of_square_brackets
    (hAll : ∀ ψ : PChar, LevelBracketWindows (Level.cyc ψ) 2) :
    AllLevelsWindowBound (3 / 2) :=
  fun ψ => levelWindowBound_three_halves_of_square_brackets (hAll ψ)

/-- `TopShape` / `TopPlug` bridge producing `ThetaSlopeContract S`:
any realization that turns `VWinAt S ψ 401` into `LevelBracketWindows (Level.cyc ψ) (3 / 2)`
instantiates `ThetaSlopeContract S`. -/
theorem topPlug_thetaSlopeContract (S : SelmerSystem)
    (hTopShape : ∀ ψ : PChar, VWinAt S ψ 401 → LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    ThetaSlopeContract S where
  windows_of_vwin hV :=
    allLevelsWindowBound_three_halves_of_brackets fun ψ => hTopShape ψ (hV ψ)

/-- End-to-end `TopPlug` theorem (`ZeroFreeAll`) at `la = 3 / 2`:
combining `VWin S`, `TopShape` bracket-window production, and `AnalyticBridgeContract`. -/
theorem topPlug_zeroFreeAll {S : SelmerSystem}
    (hAnalytic : AnalyticBridgeContract)
    (hV : VWin S)
    (hTopShape : ∀ ψ : PChar, VWinAt S ψ 401 → LevelBracketWindows (Level.cyc ψ) (3 / 2)) :
    ZeroFreeAll :=
  hAnalytic.zeroFreeAll_of_windows (3 / 2) (by norm_num)
    ((topPlug_thetaSlopeContract S hTopShape).windows_of_vwin hV)

end ZeroDensityWindow
end RHDirect

end
