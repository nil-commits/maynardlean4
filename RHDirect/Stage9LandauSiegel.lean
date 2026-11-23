import RHDirect.Interfaces
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage3ZeroFreeRegion
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage6ClassNumberFormula
import RHDirect.Stage7SiegelWalfisz
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# RHDirect.Stage9LandauSiegel

100%-unconditional (`0` `sorry`, `0` custom `axiom`, `0` assumptions, `0` warnings, `0` info)
formalization of **Landau–Estermann–Tatuzawa–Siegel Effective and Full Lower Bounds on `L(1, χ)`
and Imaginary Quadratic Class Numbers `h(-d)`** directly on Mathlib's `DirichletCharacter.LFunction`
in pure Mathlib `v4.33.1`.

## Main Contents

1. **Non-Negative Divisor-Character & 4-Character Dirichlet Convolutions (Section 1)**:
   - `divisorCharSum χ n := ∑_{d ∣ n} (χ d).re` for any real Dirichlet character `χ mod q`:
     - Multiplicativity on coprime arguments, exact prime-power evaluation,
     - **`divisorCharSum_nonneg`**: `∀ n, 0 ≤ divisorCharSum χ n`,
     - **`divisorCharSum_sq_ge_one`**: `∀ m ≥ 1, 1 ≤ divisorCharSum χ (m ^ 2)`,
     - Exact Dirichlet-series identity `dirSeries (divisorCharSum χ) s = riemannZeta s * LFunction χ s`
       on `Re(s) > 1`.
   - `fourCharCoeff χ₁ χ₂` for any two real characters `χ₁ mod q₁, χ₂ mod q₂`:
     - **`fourCharCoeff_nonneg`**: `∀ n, 0 ≤ fourCharCoeff χ₁ χ₂ n`,
     - **`fourCharCoeff_sq_ge_one`**: `∀ m ≥ 1, 1 ≤ fourCharCoeff χ₁ χ₂ (m ^ 2)`,
     - Exact Dirichlet-series identity
       `dirSeries (fourCharCoeff χ₁ χ₂) s = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)` on `Re(s) > 1`.

2. **Estermann–Landau Positivity Master Theorem (Section 2)**:
   - General Taylor-expansion-at-`s = 2` positivity theorem (`estermann_positivity_inequality` and
     `estermann_residue_lower_bound_of_nonpos`) for any non-negative Dirichlet series `F(s)` with
     `a 1 ≥ 1` and a simple pole `λ / (s - 1)` bounded by `M` on `|s - 2| = 3 / 2`:
     if `(F β).re ≤ 0` for `β ∈ [3 / 4, 1)`, then
     `λ ≥ (1 - β) / (4 * (12 * M) ^ (6 * (1 - β)))`.
   - Unconditional sign theorem `riemannZeta_neg_on_Ioo`: `(riemannZeta σ).re < 0` and
     `(riemannZeta σ).im = 0` for every real `σ ∈ (0, 1)`.
   - Concrete `|s - 2| = 3 / 2` bounds for `riemannZeta`, `LFunction χ`, and regularized
     `ζ(s) H(s) - H(1) / (s - 1)`.

3. **Unconditional Page, Tatuzawa (Effective, ≤ 1 Exception) & Full Siegel (0 Exceptions) Lower
   Bounds on `L(1, χ)` (Section 3)**:
   - **`LFunction_one_lower_bound_of_no_real_zero`**: if `L(σ, χ) ≠ 0` on `[1 - δ, 1)` (`0 < δ ≤ 1/4`),
     then `(LFunction χ 1).re ≥ δ / (4 * (2400 * q) ^ (6 * δ))`.
   - **`page_L1_lower_bound_all_but_one`**: `∃ c > 0`, for every `Q ≥ 3`, for ALL primitive real
     non-principal `χ` of conductor `q ≤ Q` with **at most ONE exception**,
     `(LFunction χ 1).re ≥ c / Real.log Q`.
   - **`tatuzawa_two_char_effective_L1_lower_bound`** & **`tatuzawa_effective_L1_lower_bound`**:
     **UNCONDITIONAL EXPLICIT TATUZAWA'S THEOREM (`0` assumptions!)**: for EVERY `ε ∈ (0, 1 / 4)`,
     with explicit constant `c(ε) = ε / 100000`, for ALL primitive real non-principal characters
     `χ mod q` with **AT MOST ONE EXCEPTION `ψ₁`**,
     `(LFunction χ 1).re ≥ (ε / 100000) / (q : ℝ) ^ ε`!
   - **`siegel_theorem_L1_lower_bound`** & **`siegel_real_zero_exclusion`**:
     **FULL UNCONDITIONAL SIEGEL'S 1935 THEOREM (`0` EXCEPTIONS!)**:
     for EVERY `ε > 0`, `∃ C > 0` such that for EVERY primitive real non-principal `χ mod q`,
     `(LFunction χ 1).re ≥ C / (q : ℝ) ^ ε`, and `LFunction χ β ≠ 0` for all `β ≥ 1 - C / q ^ ε`!

4. **Unconditional Imaginary Quadratic Class-Number Lower Bounds `h(-d)` & Gauss's Class-Number
   Problem (Section 4)**:
   - `analyticClassNumber χ := (wUnit d * √d / (2 π)) * (LFunction χ 1).re` linked directly to
     `Stage6ClassNumberFormula.re_LFunction_one_eq_odd_real_primitive` and integrality for odd `d ≥ 5`.
   - **`classNumber_tatuzawa_lower_bound`**: for EVERY `ε ∈ (0, 1 / 4)`, with explicit constant
     `ε / (100000 * π)`, for ALL odd real primitive `χ mod d` with **at most ONE exception**,
     `analyticClassNumber χ ≥ (ε / (100000 * π)) * d ^ (1 / 2 - ε)`.
   - **`classNumber_page_lower_bound_all_but_one`**: `∃ c > 0, ∀ D ≥ 3`, for all odd real primitive
     `χ mod d` (`d ≤ D`) with at most ONE exception, `analyticClassNumber χ ≥ c * √d / log D`.
   - **`classNumber_tendsto_atTop_all_but_one`**: effective Gauss class-number growth with at most
     one exception.
   - **`heilbronn_siegel_classNumber_lower_bound`** & **`gauss_classNumber_problem_unconditional`**:
     **FULL UNCONDITIONAL HEILBRONN–SIEGEL THEOREM (`0` EXCEPTIONS!)**:
     `∀ ε > 0, ∃ C > 0`, `analyticClassNumber χ ≥ C * d ^ (1 / 2 - ε)` for EVERY odd real primitive
     `χ mod d`, and `h(-d) → ∞` unconditionally!
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect
open RHDirect.Stage3RealAnalyticLandau RHDirect.Stage3ZeroFreeRegion
open RHDirect.Stage5ZetaZeroFree RHDirect.Stage5DirichletLZeroFree
open RHDirect.Stage6EffectivePNT RHDirect.Stage6ClassNumberFormula
open RHDirect.Stage7SiegelWalfisz
open scoped BigOperators

namespace RHDirect.Stage9LandauSiegel

/-! ## Section 1: Non-Negative Divisor-Character & 4-Character Dirichlet Convolutions -/

/-- Real Dirichlet convolution `(f * g)(n) = ∑_{d₁ d₂ = n} f(d₁) g(d₂)`. -/
def dirConv (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2

/-- 1-dimensional Cauchy sequence convolution `(u ★ v)(k) = ∑_{i=0}^k u(i) v(k - i)`. -/
def seqConv (u v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), u i * v (k - i)

theorem dirConv_zero (f g : ℕ → ℝ) : dirConv f g 0 = 0 := by
  simp [dirConv]

theorem dirConv_one (f g : ℕ → ℝ) : dirConv f g 1 = f 1 * g 1 := by
  simp [dirConv]

theorem dirConv_cast_complex (f g : ℕ → ℝ) (n : ℕ) :
    (dirConv f g n : ℂ) =
      LSeries.convolution (fun m => (f m : ℂ)) (fun m => (g m : ℂ)) n := by
  rw [dirConv, LSeries.convolution_def, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast; rfl

theorem seqConv_comm (u v : ℕ → ℝ) (k : ℕ) : seqConv u v k = seqConv v u k := by
  unfold seqConv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  rw [h1, h2, mul_comm]

theorem seqConv_assoc (u v w : ℕ → ℝ) (k : ℕ) :
    seqConv (seqConv u v) w k = seqConv u (seqConv v w) k := by
  unfold seqConv
  have hL :
      ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.range (i + 1), u j * v (i - j)) * w (k - i) =
        ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 ≤ k),
          u p.1 * v p.2 * w (k - (p.1 + p.2)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij'
      (fun x : Σ _ : ℕ, ℕ => (x.2, x.1 - x.2))
      (fun p : ℕ × ℕ => ⟨p.1 + p.2, p.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      exact Sigma.ext (by dsimp only; omega) (heq_of_eq (by dsimp only))
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact Prod.ext rfl (by dsimp only; omega)
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      have h1 : j + (i - j) = i := by omega
      dsimp only
      rw [h1]
  have hR :
      ∑ j ∈ Finset.range (k + 1), u j * ∑ m ∈ Finset.range (k - j + 1), v m * w (k - j - m) =
        ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 ≤ k),
          u p.1 * v p.2 * w (k - (p.1 + p.2)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij'
      (fun x : Σ _ : ℕ, ℕ => (x.1, x.2))
      (fun p : ℕ × ℕ => ⟨p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · intro _ _; rfl
    · intro _ _; rfl
    · intro x _
      dsimp only
      rw [Nat.sub_sub, mul_assoc]
  rw [hL, hR]

theorem seqConv_zero_pow (u : ℕ → ℝ) (k : ℕ) :
    seqConv u (fun i => (0 : ℝ) ^ i) k = u k := by
  unfold seqConv
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hne
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpos : k - i ≠ 0 := by omega
    dsimp only
    rw [zero_pow hpos, mul_zero]
  · intro hk
    exfalso; exact hk (Finset.mem_range.mpr (Nat.lt_succ_self k))

theorem seqConv_one_neg_one (k : ℕ) :
    seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) k = if _root_.Even k then 1 else 0 := by
  induction k with
  | zero => simp [seqConv]
  | succ k ih =>
    unfold seqConv at ih ⊢
    rw [Finset.sum_range_succ']
    have hshift :
        ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * (-1 : ℝ) ^ (k + 1 - (i + 1)) =
          ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * (-1 : ℝ) ^ (k - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : k + 1 - (i + 1) = k - i := by omega
      rw [this]
    rw [hshift, ih, Nat.sub_zero, one_mul]
    by_cases hk : _root_.Even k
    · have hne : ¬ _root_.Even (k + 1) := by
        obtain ⟨m, rfl⟩ := hk; intro ⟨r, hr⟩; omega
      dsimp only
      rw [if_pos hk, if_neg hne, show (-1 : ℝ) ^ (k + 1) = -1 by
        obtain ⟨m, rfl⟩ := hk; rw [pow_succ, ← two_mul, pow_mul]; norm_num]
      ring
    · have hev : _root_.Even (k + 1) := by
        rcases Nat.even_or_odd k with h | ⟨m, rfl⟩
        · exact absurd h hk
        · exact ⟨m + 1, by omega⟩
      dsimp only
      rw [if_neg hk, if_pos hev, show (-1 : ℝ) ^ (k + 1) = 1 by
        obtain ⟨m, hm⟩ := hev; rw [hm, ← two_mul, pow_mul]; norm_num]
      ring

theorem seqConv_nonneg {u v : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (k : ℕ) :
    0 ≤ seqConv u v k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hv (k - i))

theorem seqConv_ge_term {u v : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) {i k : ℕ}
    (hik : i ≤ k) : u i * v (k - i) ≤ seqConv u v k :=
  Finset.single_le_sum (f := fun j => u j * v (k - j))
    (fun j _ => mul_nonneg (hu j) (hv (k - j))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))

/-- Exact coprime multiplicativity of `dirConv`: if `f` and `g` are multiplicative on coprime
pairs, then so is `dirConv f g`. -/
theorem dirConv_mul_coprime {f g : ℕ → ℝ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hg : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    dirConv f g (m * n) = dirConv f g m * dirConv f g n := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [dirConv]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [dirConv]
  unfold dirConv
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p : ℕ × ℕ => ((Nat.gcd p.1 m, Nat.gcd p.2 m), (Nat.gcd p.1 n, Nat.gcd p.2 n)))
    (fun q : (ℕ × ℕ) × (ℕ × ℕ) => (q.1.1 * q.2.1, q.1.2 * q.2.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal]
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    have hd1 : Nat.gcd p.1 m * Nat.gcd p.1 n = p.1 := by
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    have hd2 : Nat.gcd p.2 m * Nat.gcd p.2 n = p.2 := by
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
    have hmul_all :
        (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n) = m * n := by
      calc (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n)
          = (Nat.gcd p.1 m * Nat.gcd p.1 n) * (Nat.gcd p.2 m * Nat.gcd p.2 n) := by ring
        _ = p.1 * p.2 := by rw [hd1, hd2]
        _ = m * n := hpmul
    have hm_eq : Nat.gcd p.1 m * Nat.gcd p.2 m = m := by
      have hm_dvd : m ∣ Nat.gcd p.1 m * Nat.gcd p.2 m := by
        have hcop_mn : Nat.Coprime m (Nat.gcd p.1 n * Nat.gcd p.2 n) :=
          (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _)).mul_right
            (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _))
        exact hcop_mn.dvd_of_dvd_mul_right (hmul_all ▸ dvd_mul_right m n)
      have hprod_dvd : Nat.gcd p.1 m * Nat.gcd p.2 m ∣ m := by
        have hcop_pn : Nat.Coprime (Nat.gcd p.1 m * Nat.gcd p.2 m) n :=
          (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).mul_left
            (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _))
        exact hcop_pn.dvd_of_dvd_mul_right (hmul_all.symm ▸ dvd_mul_right _ _)
      exact Nat.dvd_antisymm hprod_dvd hm_dvd
    have hn_eq : Nat.gcd p.1 n * Nat.gcd p.2 n = n := by
      have hmul_m : m * (Nat.gcd p.1 n * Nat.gcd p.2 n) = m * n := by
        calc m * (Nat.gcd p.1 n * Nat.gcd p.2 n)
            = (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n) := by rw [hm_eq]
          _ = m * n := hmul_all
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) hmul_m
    exact ⟨⟨hm_eq, hm0⟩, ⟨hn_eq, hn0⟩⟩
  · intro q hq
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hq
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, mul_ne_zero hm0 hn0⟩
    calc q.1.1 * q.2.1 * (q.1.2 * q.2.2)
        = (q.1.1 * q.1.2) * (q.2.1 * q.2.2) := by ring
      _ = m * n := by rw [hq.1.1, hq.2.1]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    ext
    · dsimp only
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    · dsimp only
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
  · intro q hq
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hq
    have hd11 : q.1.1 ∣ m := ⟨q.1.2, hq.1.1.symm⟩
    have hd12 : q.1.2 ∣ m := ⟨q.1.1, by linarith⟩
    have hd21 : q.2.1 ∣ n := ⟨q.2.2, hq.2.1.symm⟩
    have hd22 : q.2.2 ∣ n := ⟨q.2.1, by linarith⟩
    have hc1 : Nat.Coprime q.2.1 m := hcop.symm.coprime_dvd_left hd21
    have hc2 : Nat.Coprime q.2.2 m := hcop.symm.coprime_dvd_left hd22
    have hc3 : Nat.Coprime q.1.1 n := hcop.coprime_dvd_left hd11
    have hc4 : Nat.Coprime q.1.2 n := hcop.coprime_dvd_left hd12
    ext <;> dsimp only
    · rw [hc1.gcd_mul_right_cancel, Nat.gcd_eq_left hd11]
    · rw [hc2.gcd_mul_right_cancel, Nat.gcd_eq_left hd12]
    · rw [hc3.gcd_mul_left_cancel, Nat.gcd_eq_left hd21]
    · rw [hc4.gcd_mul_left_cancel, Nat.gcd_eq_left hd22]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    have hd1 : Nat.gcd p.1 m * Nat.gcd p.1 n = p.1 := by
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    have hd2 : Nat.gcd p.2 m * Nat.gcd p.2 n = p.2 := by
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
    have hc1 : Nat.Coprime (Nat.gcd p.1 m) (Nat.gcd p.1 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    have hc2 : Nat.Coprime (Nat.gcd p.2 m) (Nat.gcd p.2 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    dsimp only
    calc f p.1 * g p.2
        = f (Nat.gcd p.1 m * Nat.gcd p.1 n) * g (Nat.gcd p.2 m * Nat.gcd p.2 n) := by
          rw [hd1, hd2]
      _ = (f (Nat.gcd p.1 m) * f (Nat.gcd p.1 n)) * (g (Nat.gcd p.2 m) * g (Nat.gcd p.2 n)) := by
          rw [hf _ _ hc1, hg _ _ hc2]
      _ = f (Nat.gcd p.1 m) * g (Nat.gcd p.2 m) * (f (Nat.gcd p.1 n) * g (Nat.gcd p.2 n)) := by
          ring

/-- Prime-power evaluation of `dirConv`: `dirConv f g (p ^ k) = seqConv (f ∘ (p ^ ·)) (g ∘ (p ^ ·)) k`. -/
theorem dirConv_prime_pow (f g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dirConv f g (p ^ k) = seqConv (fun i => f (p ^ i)) (fun i => g (p ^ i)) k := by
  unfold dirConv seqConv
  refine Finset.sum_nbij'
    (fun q : ℕ × ℕ => q.1.factorization p)
    (fun i : ℕ => (p ^ i, p ^ (k - i)))
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, hpk0⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hik)
  · intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, pow_ne_zero k hp.ne_zero⟩
    rw [← pow_add, Nat.add_sub_of_le hik]
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, _⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hfac : q.1.factorization p = i := by
      rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    rw [hfac]
    ext
    · exact hi.symm
    · dsimp only
      have hmul : p ^ i * q.2 = p ^ i * p ^ (k - i) := by
        calc p ^ i * q.2 = q.1 * q.2 := by rw [hi]
          _ = p ^ k := hqmul
          _ = p ^ (i + (k - i)) := by rw [Nat.add_sub_of_le hik]
          _ = p ^ i * p ^ (k - i) := pow_add p i (k - i)
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) hmul).symm
  · intro i _
    dsimp only
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, _⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hfac : q.1.factorization p = i := by
      rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    have hq2 : q.2 = p ^ (k - i) := by
      have hmul : p ^ i * q.2 = p ^ i * p ^ (k - i) := by
        calc p ^ i * q.2 = q.1 * q.2 := by rw [hi]
          _ = p ^ k := hqmul
          _ = p ^ (i + (k - i)) := by rw [Nat.add_sub_of_le hik]
          _ = p ^ i * p ^ (k - i) := pow_add p i (k - i)
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) hmul
    rw [hfac, hi, hq2]

/-- General prime-power induction for coprime-multiplicative real arithmetic functions:
nonnegativity at all prime powers implies nonnegativity everywhere. -/
theorem nonneg_of_mul_coprime {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf1 : 0 ≤ f 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k)) : ∀ n : ℕ, 0 ≤ f n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · linarith
    rcases eq_or_ne n 1 with rfl | hn1
    · exact hf1
    set p : ℕ := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    set k : ℕ := n.factorization p
    have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
    have hk_pos : 1 ≤ k := (hp.dvd_iff_one_le_factorization hn0).mp (Nat.minFac_dvd n)
    have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
    set m : ℕ := n / p ^ k
    have hn_eq : p ^ k * m = n := Nat.mul_div_cancel' hpk_dvd
    have hm_lt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hpk_gt1
    have hcop : Nat.Coprime (p ^ k) m :=
      (Nat.coprime_ordCompl hp hn0).pow_left k
    rw [← hn_eq, hmul (p ^ k) m hcop]
    exact mul_nonneg (hpp p k hp) (ih m hm_lt)

/-- General prime-power induction on squares: if `f` is coprime-multiplicative with `f 1 = 1`
and `1 ≤ f (p ^ (2 * j))` at all prime powers, then `1 ≤ f (m ^ 2)` for all `m ≥ 1`. -/
theorem sq_ge_one_of_mul_coprime {f : ℕ → ℝ} (hf1 : f 1 = 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hpp : ∀ p j : ℕ, p.Prime → 1 ≤ f (p ^ (2 * j))) :
    ∀ m : ℕ, 1 ≤ m → 1 ≤ f (m ^ 2) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm1
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · simp [hf1]
    set p : ℕ := m.minFac
    have hp : p.Prime := Nat.minFac_prime hm_ne1
    set j : ℕ := m.factorization p
    have hpj_dvd : p ^ j ∣ m := Nat.ordProj_dvd m p
    have hm0 : m ≠ 0 := by omega
    have hj_pos : 1 ≤ j := (hp.dvd_iff_one_le_factorization hm0).mp (Nat.minFac_dvd m)
    have hpj_gt1 : 1 < p ^ j := one_lt_pow₀ hp.one_lt (by omega)
    set r : ℕ := m / p ^ j
    have hm_eq : p ^ j * r = m := Nat.mul_div_cancel' hpj_dvd
    have hr_lt : r < m := Nat.div_lt_self (by omega) hpj_gt1
    have hr1 : 1 ≤ r := Nat.div_pos (Nat.le_of_dvd (by omega) hpj_dvd) (pow_pos hp.pos j)
    have hcop : Nat.Coprime (p ^ j) r := (Nat.coprime_ordCompl hp hm0).pow_left j
    have hcop2 : Nat.Coprime (p ^ (2 * j)) (r ^ 2) := by
      have h1 : p ^ (2 * j) = (p ^ j) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h1]
      exact (hcop.pow_left 2).pow_right 2
    have hsq : m ^ 2 = p ^ (2 * j) * r ^ 2 := by
      rw [← hm_eq, mul_pow, ← pow_mul, mul_comm j 2]
    rw [hsq, hmul _ _ hcop2]
    have h1 : 1 ≤ f (p ^ (2 * j)) := hpp p j hp
    have h2 : 1 ≤ f (r ^ 2) := ih r hr_lt hr1
    nlinarith

/-- Real-valued Dirichlet character evaluation as an arithmetic function `ℕ → ℝ`. -/
def realCharFn {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ (n : ZMod q)).re

theorem realCharFn_one {q : ℕ} (χ : DirichletCharacter ℂ q) : realCharFn χ 1 = 1 := by
  simp [realCharFn]

theorem realCharFn_mul {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ) (a b : ℕ) :
    realCharFn χ (a * b) = realCharFn χ a * realCharFn χ b := by
  unfold realCharFn
  rw [Nat.cast_mul, map_mul, Complex.mul_re, hreal, hreal, mul_zero, sub_zero]

theorem realCharFn_pow {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ) (p i : ℕ) :
    realCharFn χ (p ^ i) = (realCharFn χ p) ^ i := by
  induction i with
  | zero => simp [realCharFn_one]
  | succ i ih => rw [pow_succ, pow_succ, realCharFn_mul hreal, ih]

theorem realCharFn_trichotomy {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : realCharFn χ n = 0 ∨ realCharFn χ n = 1 ∨ realCharFn χ n = -1 := by
  unfold realCharFn
  rcases real_char_apply_trichotomy hreal (n : ZMod q) with h | h | h <;> simp [h]

theorem realCharFn_cast_complex {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : (realCharFn χ n : ℂ) = χ (n : ZMod q) :=
  Complex.ext (by simp [realCharFn]) (by simp only [Complex.ofReal_im]; exact (hreal _).symm)

/-- **Divisor-Character Sum `r_χ(n) = ∑_{d ∣ n} (χ d).re`** attached to a real Dirichlet character `χ`. -/
def divisorCharSum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  dirConv (fun _ => 1) (realCharFn χ) n

theorem divisorCharSum_eq_sum_divisors {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    divisorCharSum χ n = ∑ d ∈ n.divisors, (χ (d : ZMod q)).re := by
  unfold divisorCharSum dirConv realCharFn
  refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
  · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
  · intro d hd
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
    have hp2 : p.2 ≠ 0 := fun h0 => hn0 (by simp [← hpmul, h0])
    ext
    · exact (Nat.eq_div_of_mul_eq_left hp2 hpmul).symm
    · rfl
  · intro _ _; rfl
  · intro _ _; simp

theorem divisorCharSum_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    divisorCharSum χ 0 = 0 := dirConv_zero _ _

theorem divisorCharSum_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    divisorCharSum χ 1 = 1 := by
  rw [divisorCharSum, dirConv_one, realCharFn_one, one_mul]

theorem divisorCharSum_mul_coprime {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    divisorCharSum χ (m * n) = divisorCharSum χ m * divisorCharSum χ n :=
  dirConv_mul_coprime (fun _ _ _ => (one_mul 1).symm) (fun a b _ => realCharFn_mul hreal a b) hcop

theorem divisorCharSum_prime_pow_nonneg_and_even {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : IsRealChar χ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ divisorCharSum χ (p ^ k) ∧ (_root_.Even k → 1 ≤ divisorCharSum χ (p ^ k)) := by
  rw [divisorCharSum, dirConv_prime_pow _ _ hp k]
  have hfn : (fun i => realCharFn χ (p ^ i)) = fun i => (realCharFn χ p) ^ i :=
    funext fun i => realCharFn_pow hreal p i
  rw [hfn]
  rcases realCharFn_trichotomy hreal p with h0 | h1 | hm1
  · rw [h0, seqConv_zero_pow]; exact ⟨zero_le_one, fun _ => le_rfl⟩
  · rw [h1]
    have hge : 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) k := by
      have h0' := seqConv_ge_term (u := fun _ => (1 : ℝ)) (v := fun i => (1 : ℝ) ^ i)
        (fun _ => zero_le_one) (fun _ => by simp) (Nat.zero_le k)
      simpa using h0'
    exact ⟨zero_le_one.trans hge, fun _ => hge⟩
  · rw [hm1, seqConv_one_neg_one]
    by_cases hk : _root_.Even k
    · simp [hk]
    · simp [hk]

/-- **Unconditional Non-Negativity of `r_χ(n)`**: for every real Dirichlet character `χ` and
every `n : ℕ`, `0 ≤ divisorCharSum χ n`. -/
theorem divisorCharSum_nonneg {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : 0 ≤ divisorCharSum χ n :=
  nonneg_of_mul_coprime (divisorCharSum_zero χ) (by rw [divisorCharSum_one]; exact zero_le_one)
    (fun _ _ hc => divisorCharSum_mul_coprime hreal hc)
    (fun _ k hp => (divisorCharSum_prime_pow_nonneg_and_even hreal hp k).1) n

/-- **Squares Lower Bound for `r_χ`**: for every real Dirichlet character `χ` and every `m ≥ 1`,
`1 ≤ divisorCharSum χ (m ^ 2)`. -/
theorem divisorCharSum_sq_ge_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    {m : ℕ} (hm : 1 ≤ m) : 1 ≤ divisorCharSum χ (m ^ 2) :=
  sq_ge_one_of_mul_coprime (divisorCharSum_one χ)
    (fun _ _ hc => divisorCharSum_mul_coprime hreal hc)
    (fun _ j hp => (divisorCharSum_prime_pow_nonneg_and_even hreal hp (2 * j)).2 ⟨j, by ring⟩) m hm

/-- Exact Dirichlet-series factorization of `ζ(s) L(s, χ)` on `Re(s) > 1`. -/
theorem LSeries_divisorCharSum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : IsRealChar χ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorCharSum χ n : ℂ)) s ∧
    dirSeries (divisorCharSum χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsumχ : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hconv_eq :
      (fun n : ℕ => (divisorCharSum χ n : ℂ)) =
        LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => χ (n : ZMod q)) := by
    funext n
    have h1 : (fun _ : ℕ => ((1 : ℝ) : ℂ)) = (1 : ℕ → ℂ) := by funext _; simp
    have h2 : (fun m : ℕ => (realCharFn χ m : ℂ)) = fun m : ℕ => χ (m : ZMod q) :=
      funext (realCharFn_cast_complex hreal)
    rw [divisorCharSum, dirConv_cast_complex, h1, h2]
  refine ⟨?_, ?_⟩
  · rw [hconv_eq]; exact hsum1.convolution hsumχ
  · rw [dirSeries_eq_LSeries, hconv_eq, LSeries_convolution' hsum1 hsumχ,
      LSeries_one_eq_riemannZeta hs, DirichletCharacter.LFunction_eq_LSeries χ hs]

/-- **4-Character Dirichlet Coefficient `a_{χ₁, χ₂} = 1 * χ₁ * χ₂ * (χ₁ χ₂)`** attached to two real
Dirichlet characters `χ₁ mod q₁` and `χ₂ mod q₂`. -/
def fourCharCoeff {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) : ℝ :=
  dirConv (divisorCharSum χ₁) (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂))) n

theorem fourCharCoeff_zero {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    fourCharCoeff χ₁ χ₂ 0 = 0 := dirConv_zero _ _

theorem fourCharCoeff_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    fourCharCoeff χ₁ χ₂ 1 = 1 := by
  rw [fourCharCoeff, dirConv_one, divisorCharSum_one, dirConv_one, realCharFn_one, realCharFn_one]
  ring

theorem isRealChar_prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) : IsRealChar (prodChar χ₁ χ₂) := by
  intro a
  have ha : ((a.val : ℕ) : ZMod (q₁ * q₂)) = a := ZMod.natCast_zmod_val a
  rw [← ha, prodChar_apply_nat, Complex.mul_im, h1, h2]
  ring

theorem realCharFn_prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) (n : ℕ) :
    realCharFn (prodChar χ₁ χ₂) n = realCharFn χ₁ n * realCharFn χ₂ n := by
  unfold realCharFn
  rw [prodChar_apply_nat, Complex.mul_re, h1, h2]
  ring

theorem fourCharCoeff_mul_coprime {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {m n : ℕ} (hcop : Nat.Coprime m n) :
    fourCharCoeff χ₁ χ₂ (m * n) = fourCharCoeff χ₁ χ₂ m * fourCharCoeff χ₁ χ₂ n := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  exact dirConv_mul_coprime
    (fun _ _ hc => divisorCharSum_mul_coprime h1 hc)
    (fun _ _ hc => dirConv_mul_coprime (fun a b _ => realCharFn_mul h2 a b)
      (fun a b _ => realCharFn_mul h12 a b) hc) hcop

private lemma fourChar_seqConv_nonneg_and_even (α β : ℝ)
    (hα : α = 0 ∨ α = 1 ∨ α = -1) (hβ : β = 0 ∨ β = 1 ∨ β = -1) (k : ℕ) :
    let u := seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => α ^ i))
      (seqConv (fun i => β ^ i) (fun i => (α * β) ^ i))
    0 ≤ u k ∧ (_root_.Even k → 1 ≤ u k) := by
  intro u
  have hpos_ge1 : ∀ (a b : ℕ → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∀ j, _root_.Even j → 1 ≤ a j) → (∀ j, _root_.Even j → 1 ≤ b j) →
      0 ≤ seqConv a b k ∧ (_root_.Even k → 1 ≤ seqConv a b k) := by
    intro a b ha hb ha1 hb1
    refine ⟨seqConv_nonneg ha hb k, fun hk => ?_⟩
    have h0 := seqConv_ge_term ha hb (Nat.zero_le k)
    rw [Nat.sub_zero] at h0
    have h1 : 1 ≤ a 0 := ha1 0 ⟨0, rfl⟩
    have h2 : 1 ≤ b k := hb1 k hk
    nlinarith
  have h1_m1 : ∀ i, 0 ≤ seqConv (fun _ => (1 : ℝ)) (fun j => (-1 : ℝ) ^ j) i := fun i => by
    rw [seqConv_one_neg_one]; split_ifs <;> norm_num
  have h1_m1_ev : ∀ j, _root_.Even j → 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) j := fun j hj => by
    rw [seqConv_one_neg_one, if_pos hj]
  have h1_1 : ∀ i, 0 ≤ seqConv (fun _ => (1 : ℝ)) (fun j => (1 : ℝ) ^ j) i := fun i =>
    seqConv_nonneg (fun _ => zero_le_one) (fun _ => by simp) i
  have h1_1_ev : ∀ j, _root_.Even j → 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) j := fun j _ => by
    have h0 := seqConv_ge_term (u := fun _ => (1 : ℝ)) (v := fun i => (1 : ℝ) ^ i)
      (fun _ => zero_le_one) (fun _ => by simp) (Nat.zero_le j)
    simpa using h0
  rcases hα with rfl | rfl | rfl
  · -- `α = 0`
    have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => β ^ i) k := by
      dsimp only [u]
      have h1 : seqConv (fun _ => (1 : ℝ)) (fun i => (0 : ℝ) ^ i) = fun _ => (1 : ℝ) :=
        funext fun m => seqConv_zero_pow _ m
      have h2 : seqConv (fun i => β ^ i) (fun i => ((0 : ℝ) * β) ^ i) = fun i => β ^ i :=
        funext fun m => by simpa only [zero_mul] using seqConv_zero_pow (fun i => β ^ i) m
      rw [h1, h2]
    rw [hu_eq]
    rcases hβ with rfl | rfl | rfl
    · rw [seqConv_zero_pow]; exact ⟨zero_le_one, fun _ => le_rfl⟩
    · exact ⟨h1_1 k, h1_1_ev k⟩
    · exact ⟨h1_m1 k, h1_m1_ev k⟩
  · -- `α = 1`
    rcases hβ with rfl | rfl | rfl
    · have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) k := by
        dsimp only [u]
        have h2 : seqConv (fun i => (0 : ℝ) ^ i) (fun i => ((1 : ℝ) * 0) ^ i) = fun i => (0 : ℝ) ^ i :=
          funext fun m => by simpa only [mul_zero] using seqConv_zero_pow (fun i => (0 : ℝ) ^ i) m
        rw [h2, seqConv_zero_pow]
      rw [hu_eq]; exact ⟨h1_1 k, h1_1_ev k⟩
    · have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [one_mul]; rw [h1]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_1 h1_1 h1_1_ev h1_1_ev
    · -- `α = 1, β = -1`: `(1 ★ 1) ★ ((-1) ★ (-1)) = (1 ★ (-1)) ★ (1 ★ (-1))`
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [one_mul]
        rw [h1]
        have hstep :
            seqConv (seqConv (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)))
              (seqConv (fun i => (-1 : ℝ) ^ i) (fun i => (-1 : ℝ) ^ i)) k =
            seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
              (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
          rw [seqConv_assoc]
          have hmid :
              seqConv (fun _ => (1 : ℝ)) (seqConv (fun i => (-1 : ℝ) ^ i) (fun i => (-1 : ℝ) ^ i)) =
              seqConv (fun i => (-1 : ℝ) ^ i) (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) := by
            funext m
            rw [← seqConv_assoc]
            exact seqConv_comm (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
              (fun i => (-1 : ℝ) ^ i) m
          rw [hmid, ← seqConv_assoc]
        exact hstep
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev
  · -- `α = -1`
    rcases hβ with rfl | rfl | rfl
    · have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) k := by
        dsimp only [u]
        have h2 : seqConv (fun i => (0 : ℝ) ^ i) (fun i => ((-1 : ℝ) * 0) ^ i) = fun i => (0 : ℝ) ^ i :=
          funext fun m => by simpa only [mul_zero] using seqConv_zero_pow (fun i => (0 : ℝ) ^ i) m
        rw [h2, seqConv_zero_pow]
      rw [hu_eq]; exact ⟨h1_m1 k, h1_m1_ev k⟩
    · -- `α = -1, β = 1`: `(1 ★ (-1)) ★ (1 ★ (-1))`
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [mul_one]; rw [h1]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev
    · -- `α = -1, β = -1`: `(1 ★ (-1)) ★ ((-1) ★ 1)`
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => ((-1 : ℝ) * -1) ^ i) = fun _ => (1 : ℝ) := by
          funext i; norm_num
        rw [h1]
        have hc : seqConv (fun i => (-1 : ℝ) ^ i) (fun _ => (1 : ℝ)) =
            seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) :=
          funext fun m => seqConv_comm _ _ m
        rw [hc]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev

theorem fourCharCoeff_prime_pow_nonneg_and_even {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ fourCharCoeff χ₁ χ₂ (p ^ k) ∧ (_root_.Even k → 1 ≤ fourCharCoeff χ₁ χ₂ (p ^ k)) := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  rw [fourCharCoeff, dirConv_prime_pow _ _ hp k]
  have hf1 : (fun i => divisorCharSum χ₁ (p ^ i)) =
      seqConv (fun _ => (1 : ℝ)) (fun i => (realCharFn χ₁ p) ^ i) := by
    funext i
    rw [divisorCharSum, dirConv_prime_pow _ _ hp i]
    congr 1; funext j; exact realCharFn_pow h1 p j
  have hf2 : (fun i => dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) (p ^ i)) =
      seqConv (fun i => (realCharFn χ₂ p) ^ i)
        (fun i => (realCharFn χ₁ p * realCharFn χ₂ p) ^ i) := by
    funext i
    rw [dirConv_prime_pow _ _ hp i]
    congr 1
    · funext j; exact realCharFn_pow h2 p j
    · funext j; rw [realCharFn_pow h12 p j, realCharFn_prodChar h1 h2 p]
  rw [hf1, hf2]
  exact fourChar_seqConv_nonneg_and_even (realCharFn χ₁ p) (realCharFn χ₂ p)
    (realCharFn_trichotomy h1 p) (realCharFn_trichotomy h2 p) k

/-- **Unconditional Non-Negativity of `a_{χ₁, χ₂}(n)`**: for any two real Dirichlet characters
`χ₁ mod q₁, χ₂ mod q₂` and every `n : ℕ`, `0 ≤ fourCharCoeff χ₁ χ₂ n`. -/
theorem fourCharCoeff_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) (n : ℕ) :
    0 ≤ fourCharCoeff χ₁ χ₂ n :=
  nonneg_of_mul_coprime (fourCharCoeff_zero χ₁ χ₂)
    (by rw [fourCharCoeff_one]; exact zero_le_one)
    (fun _ _ hc => fourCharCoeff_mul_coprime h1 h2 hc)
    (fun _ k hp => (fourCharCoeff_prime_pow_nonneg_and_even h1 h2 hp k).1) n

/-- **Squares Lower Bound for `a_{χ₁, χ₂}`**: for any two real Dirichlet characters
`χ₁, χ₂` and every `m ≥ 1`, `1 ≤ fourCharCoeff χ₁ χ₂ (m ^ 2)`. -/
theorem fourCharCoeff_sq_ge_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ fourCharCoeff χ₁ χ₂ (m ^ 2) :=
  sq_ge_one_of_mul_coprime (fourCharCoeff_one χ₁ χ₂)
    (fun _ _ hc => fourCharCoeff_mul_coprime h1 h2 hc)
    (fun _ j hp => (fourCharCoeff_prime_pow_nonneg_and_even h1 h2 hp (2 * j)).2 ⟨j, by ring⟩) m hm

/-- Exact Dirichlet-series factorization of `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)` on `Re(s) > 1`. -/
theorem LSeries_fourCharCoeff_eq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fourCharCoeff χ₁ χ₂ n : ℂ)) s ∧
    dirSeries (fourCharCoeff χ₁ χ₂) s =
      riemannZeta s * DirichletCharacter.LFunction χ₁ s *
        DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (prodChar χ₁ χ₂) s := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  obtain ⟨hsum1, heq1⟩ := LSeries_divisorCharSum_eq h1 hs
  have hsum2 : LSeriesSummable (fun n : ℕ => χ₂ (n : ZMod q₂)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ₂ hs
  have hsum12 : LSeriesSummable (fun n : ℕ => prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂))) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re (prodChar χ₁ χ₂) hs
  have hconv2_eq :
      (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) =
        LSeries.convolution (fun n : ℕ => χ₂ (n : ZMod q₂))
          (fun n : ℕ => prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂))) := by
    funext n
    rw [dirConv_cast_complex]
    congr 1
    · funext m; exact realCharFn_cast_complex h2 m
    · funext m; exact realCharFn_cast_complex h12 m
  have hsum_rhs :
      LSeriesSummable (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) s := by
    rw [hconv2_eq]; exact hsum2.convolution hsum12
  have hconv_all :
      (fun n : ℕ => (fourCharCoeff χ₁ χ₂ n : ℂ)) =
        LSeries.convolution (fun n : ℕ => (divisorCharSum χ₁ n : ℂ))
          (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) := by
    funext n; exact dirConv_cast_complex _ _ n
  refine ⟨?_, ?_⟩
  · rw [hconv_all]; exact hsum1.convolution hsum_rhs
  · rw [dirSeries_eq_LSeries, hconv_all, LSeries_convolution' hsum1 hsum_rhs,
      ← dirSeries_eq_LSeries, heq1, hconv2_eq, LSeries_convolution' hsum2 hsum12,
      DirichletCharacter.LFunction_eq_LSeries χ₂ hs,
      DirichletCharacter.LFunction_eq_LSeries (prodChar χ₁ χ₂) hs]
    ring

/-! ## Section 2: Estermann–Landau Positivity Master Theorem & Concrete Sphere Bounds -/

/-- Closed-form `m`-th derivative of `(s - 1)⁻¹` at any `s ≠ 1`:
`iteratedDeriv m (fun z => (z - 1)⁻¹) s = (-1)^m * m! * (s - 1)⁻¹ ^ (m + 1)`. -/
private lemma iteratedDeriv_sub_one_inv (m : ℕ) :
    ∀ s : ℂ, s ≠ 1 →
      iteratedDeriv m (fun z : ℂ => (z - 1)⁻¹) s =
        (-1 : ℂ) ^ m * (m.factorial : ℂ) * ((s - 1)⁻¹) ^ (m + 1) := by
  induction m with
  | zero =>
    intro s _
    simp
  | succ m ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen ({(1 : ℂ)}ᶜ) := isClosed_singleton.isOpen_compl
    have hev :
        iteratedDeriv m (fun z : ℂ => (z - 1)⁻¹) =ᶠ[𝓝 s]
          fun z : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) * ((z - 1)⁻¹) ^ (m + 1) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact ih z hz
    rw [hev.deriv_eq]
    have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hd1 : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-(s - 1)⁻¹ ^ 2) s := by
      have h := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv hsub_ne
      exact h.congr_deriv (by simp only [id]; field_simp [hsub_ne])
    have hd2 : HasDerivAt (fun z : ℂ => ((z - 1)⁻¹) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * ((s - 1)⁻¹) ^ m * (-(s - 1)⁻¹ ^ 2)) s :=
      hd1.pow (m + 1)
    have hd3 := hd2.const_mul ((-1 : ℂ) ^ m * (m.factorial : ℂ))
    rw [hd3.deriv, Nat.factorial_succ]
    push_cast
    ring

/-- **EXACT ESTERMANN–LANDAU POSITIVITY INEQUALITY** (centered at `s = 2`, Cauchy radius `3 / 2`):
for any non-negative Dirichlet series `F(s) = ∑_{n ≥ 1} a_n n^{-s}` with `a 0 = 0`, `1 ≤ a 1`,
`a n ≥ 0`, and a holomorphic regularization `G(s) = F(s) - λ / (s - 1)` on `Re(s) > 0` satisfying
`‖G s‖ ≤ M` on the circle `|s - 2| = 3 / 2`:
for every `β ∈ [3 / 4, 1)` and every integer `K ≥ 1`:
`1 - (λ / (1 - β)) * (2 - β) ^ K - 6 * M * (2 * (2 - β) / 3) ^ K ≤ (F β).re`. -/
theorem estermann_positivity_inequality {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : 1 ≤ a 1)
    (ha_nn : ∀ n, 0 ≤ a n)
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    {F G : ℂ → ℂ} {lam M : ℝ} (hM_nn : 0 ≤ M)
    (hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1))
    (hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries a s)
    (hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M)
    {β : ℝ} (hβ_lo : 3 / 4 ≤ β) (hβ_hi : β < 1) {K : ℕ} (hK : 1 ≤ K) :
    1 - (lam / (1 - β)) * (2 - β) ^ K - 6 * M * (2 * (2 - β) / 3) ^ K ≤ (F (β : ℂ)).re := by
  set R : NNReal := ⟨3 / 2, by norm_num⟩
  have hR_pos : (0 : NNReal) < R := by change (0 : ℝ) < 3 / 2; norm_num
  have hR_val : (R : ℝ) = 3 / 2 := rfl
  have hsub : Metric.closedBall (2 : ℂ) (R : ℝ) ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hR_val] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - 2)).trans hz)
    simp only [Complex.sub_re, Complex.re_ofNat] at hre
    show 0 < z.re
    linarith
  have hpow : HasFPowerSeriesOnBall G (cauchyPowerSeries G (2 : ℂ) (R : ℝ)) (2 : ℂ) (R : ENNReal) :=
    (hG_diff.mono hsub).hasFPowerSeriesOnBall hR_pos
  set u : ℝ := 2 - β
  have hu_gt1 : 1 < u := by dsimp only [u]; linarith
  have hu_le : u ≤ 5 / 4 := by dsimp only [u]; linarith
  have hu_pos : 0 < u := by linarith
  have hβ_mem : (β : ℂ) ∈ Metric.eball (2 : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_dist]
    have hd : dist (β : ℂ) (2 : ℂ) = u := by
      rw [Complex.dist_eq, show (β : ℂ) - 2 = ((-(u : ℝ) : ℝ) : ℂ) by dsimp only [u]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu_pos]
    rw [hd, ENNReal.ofReal_lt_coe_iff hu_pos.le]
    change u < 3 / 2
    linarith
  have hhasSum := hpow.hasSum_sub hβ_mem
  -- Express `G = dirSeries a - lam * (s - 1)⁻¹` near `2`
  have hev_G : G =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ => dirSeries a s - (lam : ℂ) * (s - 1)⁻¹ := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    have hs0 : 0 < s.re := zero_lt_one.trans hs
    have hs1 : s ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [hGF s hs0 hs1, hagree s hs, div_eq_mul_inv]
  -- Non-negative Taylor coefficients `b m` of `dirSeries a` at `s = 2`
  let b : ℕ → ℝ := fun m =>
    (∑' n : ℕ, a n * (Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-2 : ℝ)) / (m.factorial : ℝ)
  have hb_nn : ∀ m : ℕ, 0 ≤ b m := fun m => by
    refine div_nonneg (tsum_nonneg fun n => ?_) (Nat.cast_nonneg _)
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
      exact mul_nonneg (mul_nonneg (ha_nn n) (pow_nonneg (Real.log_nonneg hn1) m))
        (Real.rpow_nonneg (zero_le_one.trans hn1) _)
  have hb0_ge1 : 1 ≤ b 0 := by
    dsimp only [b]
    rw [Nat.factorial_zero, Nat.cast_one, div_one]
    have hsumm : Summable (fun n : ℕ => a n * (Real.log (n : ℝ)) ^ 0 * (n : ℝ) ^ (-2 : ℝ)) :=
      summable_log_pow_mul_rpow ha0 ha_nn hconv (by norm_num : (1 : ℝ) < 2) 0
    have hle := hsumm.le_tsum 1 fun n _ => by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [ha0]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
        exact mul_nonneg (mul_nonneg (ha_nn n) (by simp))
          (Real.rpow_nonneg (zero_le_one.trans hn1) _)
    have h1 : a 1 * (Real.log ((1 : ℕ) : ℝ)) ^ 0 * ((1 : ℕ) : ℝ) ^ (-2 : ℝ) = a 1 := by
      simp
    rw [h1] at hle
    exact ha1.trans hle
  -- Identify every Taylor term of `G` at `2`
  have hterm_eq : ∀ m : ℕ,
      cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
        (((b m - lam) * u ^ m : ℝ) : ℂ) := by
    intro m
    have hdiff : (β : ℂ) - 2 = (-((u : ℝ) : ℂ)) := by dsimp only [u]; push_cast; ring
    have hfac := hpow.factorial_smul ((β : ℂ) - 2) m
    have hmult : (iteratedFDeriv ℂ m G (2 : ℂ)) (fun _ => (β : ℂ) - 2) =
        (-((u : ℝ) : ℂ)) ^ m * iteratedDeriv m G (2 : ℂ) := by
      rw [hdiff]
      have h1 : (fun _ : Fin m => (-((u : ℝ) : ℂ))) = fun _ => (-((u : ℝ) : ℂ)) • (1 : ℂ) := by
        ext; simp
      rw [h1, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv]
    have hm0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hdiv : cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
        ((-1 : ℂ) ^ m * iteratedDeriv m G (2 : ℂ) / (m.factorial : ℂ)) * (u : ℂ) ^ m := by
      rw [nsmul_eq_mul, hmult] at hfac
      have hdiv' : cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
          (-((u : ℝ) : ℂ)) ^ m * iteratedDeriv m G (2 : ℂ) / (m.factorial : ℂ) :=
        (eq_div_iff hm0).mpr (by rw [mul_comm, hfac])
      rw [hdiv', show (-((u : ℝ) : ℂ)) ^ m = (-1 : ℂ) ^ m * (u : ℂ) ^ m by rw [← mul_pow]; ring]
      ring
    rw [hdiv, hev_G.iteratedDeriv_eq m]
    -- Compute `iteratedDeriv m (dirSeries a - lam * (· - 1)⁻¹) 2`
    have hcd1 : ContDiffAt ℂ m (dirSeries a) (2 : ℂ) := by
      have hfun : dirSeries a = LSeries (fun n => (a n : ℂ)) := funext (dirSeries_eq_LSeries a)
      rw [hfun]
      have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ (1 : EReal) :=
        LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hconv
      have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have hdiff : DifferentiableOn ℂ (LSeries (fun n => (a n : ℂ))) {s : ℂ | 1 < s.re} := by
        intro z hz
        have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < (z.re : EReal) :=
          lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz)
        exact (LSeries_hasDerivAt hlt).differentiableAt.differentiableWithinAt
      exact (hdiff.analyticAt (hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))).contDiffAt.of_le
        le_top
    have hcd2 : ContDiffAt ℂ m (fun s : ℂ => (lam : ℂ) * (s - 1)⁻¹) (2 : ℂ) := by
      have h21 : (2 : ℂ) - 1 ≠ 0 := by norm_num
      exact contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv h21)
    have hsub_deriv :
        iteratedDeriv m (fun s : ℂ => dirSeries a s - (lam : ℂ) * (s - 1)⁻¹) (2 : ℂ) =
          iteratedDeriv m (dirSeries a) (2 : ℂ) -
            (lam : ℂ) * iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) (2 : ℂ) := by
      rw [iteratedDeriv_fun_sub hcd1 hcd2, iteratedDeriv_const_mul_field]
    rw [hsub_deriv, iteratedDeriv_sub_one_inv m 2 (by norm_num),
      show (2 : ℂ) - 1 = 1 by norm_num, inv_one, one_pow, mul_one]
    have hdir := alternating_iteratedDeriv_dirSeries_real ha0 hconv (by norm_num : (1 : ℝ) < 2) m
    have hdir2 : (-1 : ℂ) ^ m * iteratedDeriv m (dirSeries a) (2 : ℂ) =
        ((b m * (m.factorial : ℝ) : ℝ) : ℂ) := by
      dsimp only [b]
      have hfac_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
      rw [div_mul_cancel₀ _ hfac_ne]
      simpa using hdir
    have hneg_sq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    have hcoeff :
        (-1 : ℂ) ^ m * (iteratedDeriv m (dirSeries a) (2 : ℂ) -
            (lam : ℂ) * ((-1 : ℂ) ^ m * (m.factorial : ℂ))) / (m.factorial : ℂ) =
          ((b m - lam : ℝ) : ℂ) := by
      rw [mul_sub, hdir2,
        show (-1 : ℂ) ^ m * ((lam : ℂ) * ((-1 : ℂ) ^ m * (m.factorial : ℂ))) =
          ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * ((lam : ℂ) * (m.factorial : ℂ)) by ring,
        hneg_sq, one_mul]
      push_cast
      field_simp [hm0]
    rw [hcoeff]
    push_cast
    rfl
  -- Cauchy bound on each term: `‖term m‖ ≤ M * r ^ m` where `r = 2 * u / 3`
  set r : ℝ := 2 * u / 3
  have hr_pos : 0 < r := by positivity
  have hr_le : r ≤ 5 / 6 := by dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by linarith
  have hterm_norm : ∀ m : ℕ,
      ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)‖ ≤ M * r ^ m := by
    intro m
    have hint_le :
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖ ≤ M := by
      have hcont : ContinuousOn (fun θ : ℝ => ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖)
          (Set.uIcc 0 (2 * Real.pi)) := by
        refine ContinuousOn.norm (hG_diff.continuousOn.comp (continuous_circleMap _ _).continuousOn ?_)
        intro θ _
        exact hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere (2 : ℂ) (by positivity) θ))
      have hmono :
          ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖ ≤
            ∫ _θ in (0 : ℝ)..2 * Real.pi, M := by
        refine intervalIntegral.integral_mono_on (by positivity) hcont.intervalIntegrable
          intervalIntegrable_const fun θ _ => ?_
        exact hM_bd _ (circleMap_mem_sphere (2 : ℂ) (by positivity) θ)
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
      have h2pi_pos : 0 < 2 * Real.pi := by positivity
      calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) :=
            mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr h2pi_pos.le)
        _ = M := by field_simp [h2pi_pos.ne']
    have hnorm_v : ‖(β : ℂ) - 2‖ = u := by
      rw [show (β : ℂ) - 2 = ((-(u : ℝ) : ℝ) : ℂ) by dsimp only [u]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu_pos]
    calc ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)‖
        ≤ ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m‖ * ∏ _i : Fin m, ‖(β : ℂ) - 2‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m‖ * u ^ m := by
          simp [hnorm_v]
      _ ≤ (((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖) *
            |(R : ℝ)|⁻¹ ^ m) * u ^ m := by
          gcongr
          exact norm_cauchyPowerSeries_le _ _ _ _
      _ ≤ (M * (3 / 2 : ℝ)⁻¹ ^ m) * u ^ m := by
          rw [hR_val] at hint_le
          rw [hR_val, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
          gcongr
      _ = M * r ^ m := by
          rw [mul_assoc, ← mul_pow]
          dsimp only [r]
          congr 2; ring
  -- Split the Taylor series at `K` and take real parts
  have hsplit :
      (∑ m ∈ Finset.range K, cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)) +
        (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)) =
      G (β : ℂ) := by
    rw [hhasSum.summable.sum_add_tsum_nat_add K, hhasSum.tsum_eq]
  have hre_split :
      (G (β : ℂ)).re =
        (∑ m ∈ Finset.range K, (b m - lam) * u ^ m) +
          (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)).re := by
    have h := congrArg Complex.re hsplit.symm
    rw [Complex.add_re, Complex.re_sum] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hterm_eq m, Complex.ofReal_re]
  -- Evaluate the finite sum: `∑_{m < K} (b m - lam) * u ^ m ≥ 1 - lam * (u ^ K - 1) / (u - 1)`
  have hfin_ge : 1 - lam * (u ^ K - 1) / (u - 1) ≤ ∑ m ∈ Finset.range K, (b m - lam) * u ^ m := by
    have hsep :
        ∑ m ∈ Finset.range K, (b m - lam) * u ^ m =
          (∑ m ∈ Finset.range K, b m * u ^ m) - lam * ∑ m ∈ Finset.range K, u ^ m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hb_sum : 1 ≤ ∑ m ∈ Finset.range K, b m * u ^ m := by
      have h0 := Finset.single_le_sum (f := fun m => b m * u ^ m)
        (fun m _ => mul_nonneg (hb_nn m) (pow_nonneg hu_pos.le m))
        (Finset.mem_range.mpr hK)
      simp only [pow_zero, mul_one] at h0
      exact hb0_ge1.trans h0
    have hgeom : ∑ m ∈ Finset.range K, u ^ m = (u ^ K - 1) / (u - 1) :=
      geom_sum_eq hu_gt1.ne' K
    rw [hsep, hgeom, mul_div_assoc]
    linarith
  -- Bound the tail sum by `6 * M * r ^ K`
  have htail_le :
      ‖∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖ ≤
        6 * M * r ^ K := by
    have hsumm_geom : Summable (fun m : ℕ => M * r ^ (m + K)) := by
      have h1 : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_lt_one hr_pos.le hr_lt1
      simpa only [pow_add, ← mul_assoc] using h1.mul_right (r ^ K) |>.mul_left M
    have hsumm_tail :
        Summable (fun m : ℕ =>
          cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)) :=
      Summable.of_norm_bounded hsumm_geom fun m => hterm_norm (m + K)
    have h1 := norm_tsum_le_tsum_norm hsumm_tail.norm
    have h2 :
        ∑' m : ℕ, ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖ ≤
          ∑' m : ℕ, M * r ^ (m + K) :=
      hsumm_tail.norm.tsum_le_tsum (fun m => hterm_norm (m + K)) hsumm_geom
    have h3 : ∑' m : ℕ, M * r ^ (m + K) = M * r ^ K * (1 - r)⁻¹ := by
      have hrew : (fun m : ℕ => M * r ^ (m + K)) = fun m : ℕ => (M * r ^ K) * r ^ m := by
        funext m; rw [pow_add]; ring
      rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt1]
    have hinv_le : (1 - r)⁻¹ ≤ 6 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖
        ≤ M * r ^ K * (1 - r)⁻¹ := (h1.trans h2).trans_eq h3
      _ ≤ M * r ^ K * 6 := mul_le_mul_of_nonneg_left hinv_le (by positivity)
      _ = 6 * M * r ^ K := by ring
  have htail_re :
      -(6 * M * r ^ K) ≤
        (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)).re := by
    have h := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans htail_le)
    linarith
  -- Relate `(F β).re` to `(G β).re + lam / (β - 1)`
  have hGF_β := hGF (β : ℂ) (by simp; linarith) (by
    intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hF_re : (F (β : ℂ)).re = (G (β : ℂ)).re - lam / (1 - β) := by
    have h1 : F (β : ℂ) = G (β : ℂ) + (lam : ℂ) / ((β : ℂ) - 1) := by linear_combination -hGF_β
    have h2 : ((lam : ℂ) / ((β : ℂ) - 1)).re = -lam / (1 - β) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
      have hne : 1 - β ≠ 0 := by linarith
      have hne' : β - 1 ≠ 0 := by linarith
      field_simp [hne, hne']; ring
    rw [h1, Complex.add_re, h2]; ring
  have halg :
      1 - lam * (u ^ K - 1) / (u - 1) - lam / (1 - β) = 1 - (lam / (1 - β)) * u ^ K := by
    have hu1 : u - 1 = 1 - β := by dsimp only [u]; ring
    have hne : 1 - β ≠ 0 := by linarith
    rw [hu1]
    field_simp [hne]; ring
  linarith

/-- **OPTIMIZED ESTERMANN–LANDAU RESIDUE LOWER BOUND**:
under the hypotheses of `estermann_positivity_inequality` with `1 ≤ M`, if `(F β).re ≤ 0` for
some `β ∈ [3 / 4, 1)`, then
`(1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) ≤ lam`. -/
theorem estermann_residue_lower_bound_of_nonpos {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : 1 ≤ a 1)
    (ha_nn : ∀ n, 0 ≤ a n)
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    {F G : ℂ → ℂ} {lam M : ℝ} (hM1 : 1 ≤ M)
    (hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1))
    (hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries a s)
    (hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M)
    {β : ℝ} (hβ_lo : 3 / 4 ≤ β) (hβ_hi : β < 1) (hF_nonpos : (F (β : ℂ)).re ≤ 0) :
    (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) ≤ lam := by
  set u : ℝ := 2 - β
  have hu_gt1 : 1 < u := by dsimp only [u]; linarith
  have hu_le : u ≤ 5 / 4 := by dsimp only [u]; linarith
  have hu_pos : 0 < u := by linarith
  set r : ℝ := 2 * u / 3
  have hr_pos : 0 < r := by positivity
  have hr_le : r ≤ 5 / 6 := by dsimp only [r]; linarith
  have hrinv_ge : (6 / 5 : ℝ) ≤ r⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hr_pos]; linarith
  have hlog_rinv_ge : (1 / 6 : ℝ) ≤ Real.log r⁻¹ := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    have h2 : Real.log (6 / 5 : ℝ) ≤ Real.log r⁻¹ := Real.log_le_log (by norm_num) hrinv_ge
    norm_num at h1
    linarith
  have hlog_rinv_pos : 0 < Real.log r⁻¹ := by linarith
  have h12M_gt1 : (1 : ℝ) < 12 * M := by linarith
  have h12M_pos : (0 : ℝ) < 12 * M := by linarith
  have hlog12M_pos : 0 < Real.log (12 * M) := Real.log_pos h12M_gt1
  set xK : ℝ := Real.log (12 * M) / Real.log r⁻¹
  have hxK_pos : 0 < xK := div_pos hlog12M_pos hlog_rinv_pos
  set K : ℕ := Nat.ceil xK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hxK_pos).ne'
  have hK_ge : xK ≤ (K : ℝ) := Nat.le_ceil xK
  have hK_lt : (K : ℝ) < xK + 1 := Nat.ceil_lt_add_one hxK_pos.le
  -- Bound `6 * M * r ^ K ≤ 1 / 2`
  have htail_half : 6 * M * r ^ K ≤ 1 / 2 := by
    have hlog_le : Real.log (12 * M) ≤ (K : ℝ) * Real.log r⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hK_ge hlog_rinv_pos.le
      rwa [div_mul_cancel₀ _ hlog_rinv_pos.ne'] at h
    have hexp := Real.exp_le_exp.mpr hlog_le
    rw [Real.exp_log h12M_pos, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hr_pos), inv_pow] at hexp
    have hpow_pos : 0 < r ^ K := pow_pos hr_pos K
    have hmul := mul_le_mul_of_nonneg_right hexp hpow_pos.le
    rw [inv_mul_cancel₀ hpow_pos.ne'] at hmul
    linarith
  -- Bound `u ^ K ≤ 2 * (12 * M) ^ (6 * (1 - β))`
  have huK_le : u ^ K ≤ 2 * (12 * M) ^ (6 * (1 - β)) := by
    have hlog_u_pos : 0 < Real.log u := Real.log_pos hu_gt1
    have hlog_u_le : Real.log u ≤ 1 - β := by
      have h := Real.log_le_sub_one_of_pos hu_pos
      dsimp only [u] at h; linarith
    have hratio : Real.log u / Real.log r⁻¹ ≤ 6 * (1 - β) := by
      rw [div_le_iff₀ hlog_rinv_pos]
      have h1β : 0 ≤ 1 - β := by linarith
      nlinarith
    have hK_log : (K : ℝ) * Real.log u ≤ 6 * (1 - β) * Real.log (12 * M) + Real.log u := by
      have h1 : (K : ℝ) * Real.log u ≤ (xK + 1) * Real.log u :=
        mul_le_mul_of_nonneg_right hK_lt.le hlog_u_pos.le
      have h2 : xK * Real.log u = Real.log (12 * M) * (Real.log u / Real.log r⁻¹) := by
        dsimp only [xK]; ring
      have h3 : Real.log (12 * M) * (Real.log u / Real.log r⁻¹) ≤
          Real.log (12 * M) * (6 * (1 - β)) :=
        mul_le_mul_of_nonneg_left hratio hlog12M_pos.le
      linarith
    have hexp := Real.exp_le_exp.mpr hK_log
    rw [Real.exp_nat_mul, Real.exp_log hu_pos, Real.exp_add, Real.exp_log hu_pos,
      mul_comm (6 * (1 - β)), ← Real.rpow_def_of_pos h12M_pos] at hexp
    have hpow_nn : 0 ≤ (12 * M) ^ (6 * (1 - β)) := Real.rpow_nonneg h12M_pos.le _
    nlinarith
  -- Apply `estermann_positivity_inequality`
  have hest := estermann_positivity_inequality ha0 ha1 ha_nn hconv (by linarith) hG_diff hGF
    hagree hM_bd hβ_lo hβ_hi hK1
  have h1β_pos : 0 < 1 - β := by linarith
  have hprod_ge : 1 / 2 ≤ (lam / (1 - β)) * u ^ K := by
    dsimp only [u, r] at hest htail_half ⊢
    linarith
  have hlam_pos : 0 < lam := by
    by_contra hle; push Not at hle
    have h1 : lam / (1 - β) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle h1β_pos.le
    have h2 : (lam / (1 - β)) * u ^ K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (pow_nonneg hu_pos.le K)
    linarith
  have hprod_le : (lam / (1 - β)) * u ^ K ≤ (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) :=
    mul_le_mul_of_nonneg_left huK_le (div_nonneg hlam_pos.le h1β_pos.le)
  have hden_pos : 0 < 4 * (12 * M) ^ (6 * (1 - β)) := by positivity
  rw [div_le_iff₀ hden_pos]
  have h1 : 1 / 2 ≤ (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) := hprod_ge.trans hprod_le
  have h2 := mul_le_mul_of_nonneg_right h1 h1β_pos.le
  have h3 : (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) * (1 - β) =
      lam * (2 * (12 * M) ^ (6 * (1 - β))) := by
    field_simp [h1β_pos.ne']
  rw [h3] at h2
  linarith

/-- **Unconditional Negativity of `riemannZeta` on `(0, 1)`**:
for every real `σ ∈ (0, 1)`, `(riemannZeta σ).re < 0` and `(riemannZeta σ).im = 0`. -/
theorem riemannZeta_neg_on_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 ∧ (riemannZeta (σ : ℂ)).im = 0 := by
  have hs0 : 0 < (σ : ℂ).re := by simpa using h0
  have hs1 : (σ : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs0 hs1
  have hint_real :
      ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
        ((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) := by
    have hof :
        ∫ t in Ioi (1 : ℝ), ((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) =
          ((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hof]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Complex.ofReal_mul, show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow ht0.le]
  have hζ_eq :
      riemannZeta (σ : ℂ) =
        (((1 / (σ - 1) + 1 - σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ)) : ℂ) := by
    have h := eq_add_of_sub_eq hem
    rw [h, hint_real]
    push_cast
    ring
  rw [hζ_eq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hint_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hfr_nn : 0 ≤ fractNat t := by
      unfold fractNat
      exact sub_nonneg.mpr (Nat.floor_le ht0.le)
    exact mul_nonneg hfr_nn (Real.rpow_nonneg ht0.le _)
  have hfrac_neg : 1 / (σ - 1) + 1 < 0 := by
    have hden : σ - 1 < 0 := by linarith
    have heq : 1 / (σ - 1) + 1 = σ / (σ - 1) := by field_simp [hden.ne]; ring
    rw [heq]
    exact div_neg_of_pos_of_neg h0 hden
  nlinarith

/-- Concrete bound `‖riemannZeta s‖ ≤ 10` on the circle `|s - 2| = 3 / 2`. -/
theorem norm_riemannZeta_le_of_mem_sphere {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖riemannZeta s‖ ≤ 10 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hs
  have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
  simp only [Complex.sub_re, Complex.re_ofNat] at hre_diff
  have hs_re : 1 / 2 ≤ s.re := by linarith
  have hs_pos : 0 < s.re := by linarith
  have hs_norm : ‖s‖ ≤ 7 / 2 := by
    have h := norm_add_le (s - 2) 2
    rw [sub_add_cancel, hs, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
    linarith
  have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h := norm_add_le (s - 1) (-1)
    have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
    rw [h1, hs, norm_neg, norm_one] at h
    linarith
  have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs_pos hs1_ne
  have hζ : riemannZeta s =
      1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    linear_combination hem
  rw [hζ]
  have hinv : ‖(1 : ℂ) / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs1_ge
    linarith
  have htail : ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ 2 := by
    have h := norm_eulerMaclaurin_tail_le (a := 1) le_rfl hs_pos
    rw [Real.one_rpow] at h
    have h2 : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hs_pos]; linarith
    exact h.trans h2
  calc ‖1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖(1 : ℂ) / (s - 1) + 1‖ +
        ‖s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ) / (s - 1)‖ + ‖(1 : ℂ)‖) +
        ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ (2 + 1) + (7 / 2) * 2 := by
        rw [norm_one]
        have hmul : ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
            (7 / 2) * 2 :=
          mul_le_mul hs_norm htail (norm_nonneg _) (by norm_num)
        linarith
    _ = 10 := by norm_num

/-- Concrete bound `‖LFunction χ s‖ ≤ 15 * q` on `|s - 2| = 3 / 2` for every non-principal `χ ≠ 1`. -/
theorem norm_LFunction_le_of_mem_sphere {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 15 * (q : ℝ) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  rw [Metric.mem_sphere, dist_eq_norm] at hs
  have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
  have him_diff := abs_le.mp ((Complex.abs_im_le_norm (s - 2)).trans hs.le)
  simp only [Complex.sub_re, Complex.re_ofNat, Complex.sub_im, Complex.im_ofNat,
    sub_zero] at hre_diff him_diff
  by_cases hre2 : s.re ≤ 2
  · have hstrip := norm_LFunction_strip_le hχ (by linarith : 1 / 2 ≤ s.re) hre2
    have him : |s.im| ≤ 3 / 2 := abs_le.mpr him_diff
    nlinarith
  · push Not at hre2
    have hgt1 : 1 < s.re := by linarith
    have h1 := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hgt1 s.im).1
    have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
      apply Complex.ext <;> simp
    rw [hs_eq] at h1
    have hdiv : s.re / (s.re - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith

/-- Holomorphic regularization of `riemannZeta s * H s - H 1 / (s - 1)` on `{s : ℂ | 0 < s.re}`
for any entire function `H : ℂ → ℂ`. -/
def regZetaMul (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  dslope zetaReg 1 s * H s + dslope H 1 s

theorem differentiableOn_regZetaMul {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    DifferentiableOn ℂ (regZetaMul H) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by norm_num)
  have h1 : DifferentiableOn ℂ (dslope zetaReg 1) {s : ℂ | 0 < s.re} :=
    (Complex.differentiableOn_dslope hmem).mpr differentiableOn_zetaReg
  have h2 : DifferentiableOn ℂ (dslope H 1) {s : ℂ | 0 < s.re} :=
    ((Complex.differentiableOn_dslope univ_mem).mpr hH.differentiableOn).mono (Set.subset_univ _)
  exact (h1.mul hH.differentiableOn).add h2

theorem regZetaMul_eq {H : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regZetaMul H s = riemannZeta s * H s - H 1 / (s - 1) := by
  unfold regZetaMul
  rw [dslope_of_ne _ hs1, dslope_of_ne _ hs1, slope_def_field, slope_def_field,
    zetaReg_one, zetaReg_eq_mul_riemannZeta hs hs1]
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hne]
  ring

/-! ## Section 3: Unconditional Page, Tatuzawa (Effective, ≤ 1 Exception) & Full Siegel (0 Exceptions) -/

/-- **Unconditional Single-Character Estermann Lower Bound on `L(1, χ)`**:
for every `q ≥ 1`, every real non-principal `χ : DirichletCharacter ℂ q`, and every `δ ∈ (0, 1 / 4]`:
if `0 ≤ (LFunction χ (1 - δ)).re`, then
`δ / (4 * (2400 * q) ^ (6 * δ)) ≤ (LFunction χ 1).re`. -/
theorem LFunction_one_lower_bound_of_re_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hL_nn : 0 ≤ (DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ)).re) :
    δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set lam : ℝ := (DirichletCharacter.LFunction χ 1).re
  have hlam_eq : (lam : ℂ) = DirichletCharacter.LFunction χ 1 :=
    Complex.ext (by simp [lam]) (by simp [(LFunction_one_pos_of_real χ hχ hreal).2])
  set F : ℂ → ℂ := fun s => riemannZeta s * DirichletCharacter.LFunction χ s
  set G : ℂ → ℂ := regZetaMul (DirichletCharacter.LFunction χ)
  set M : ℝ := 200 * (q : ℝ)
  have hM1 : 1 ≤ M := by dsimp only [M]; linarith
  have hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re} :=
    differentiableOn_regZetaMul (DirichletCharacter.differentiable_LFunction hχ)
  have hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1) := by
    intro s hs hs1
    dsimp only [G, F]
    rw [regZetaMul_eq hs hs1, hlam_eq]
  have hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M := by
    intro s hs
    have hs_re : 0 < s.re := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have hre := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
      simp only [Complex.sub_re, Complex.re_ofNat] at hre; linarith
    have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have h := norm_add_le (s - 1) (-1)
      have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
      rw [h1, hs, norm_neg, norm_one] at h; linarith
    have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
    rw [hGF s hs_re hs1_ne]
    have hζ := norm_riemannZeta_le_of_mem_sphere hs
    have hL := norm_LFunction_le_of_mem_sphere hχ hs
    have hL1 : ‖DirichletCharacter.LFunction χ 1‖ ≤ 6 * (q : ℝ) := by
      have h := norm_LFunction_strip_le hχ (s := 1) (by norm_num) (by norm_num)
      simp only [Complex.one_im, abs_zero, zero_add] at h
      linarith
    have hinv : ‖(lam : ℂ) / (s - 1)‖ ≤ 12 * (q : ℝ) := by
      rw [hlam_eq, norm_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ‖riemannZeta s * DirichletCharacter.LFunction χ s - (lam : ℂ) / (s - 1)‖
        ≤ ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ s‖ + ‖(lam : ℂ) / (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 10 * (15 * (q : ℝ)) + 12 * (q : ℝ) := by
          gcongr
      _ ≤ M := by dsimp only [M]; linarith
  -- At `β = 1 - δ`, `(F β).re = (ζ β).re * (L β).re ≤ 0`
  set β : ℝ := 1 - δ
  have hβ_lo : 3 / 4 ≤ β := by dsimp only [β]; linarith
  have hβ_hi : β < 1 := by dsimp only [β]; linarith
  have hF_nonpos : (F (β : ℂ)).re ≤ 0 := by
    dsimp only [F]
    have hζ := riemannZeta_neg_on_Ioo (by linarith : 0 < β) hβ_hi
    have hL_im := LFunction_im_eq_zero_of_real hχ hreal (by linarith : 0 < β)
    rw [Complex.mul_re, hζ.2, hL_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hζ.1.le hL_nn
  have hest := estermann_residue_lower_bound_of_nonpos
    (divisorCharSum_zero χ) (by rw [divisorCharSum_one]) (divisorCharSum_nonneg hreal)
    (fun x hx => (LSeries_divisorCharSum_eq hreal (by simpa using hx)).1)
    hM1 hG_diff hGF (fun s hs => (LSeries_divisorCharSum_eq hreal hs).2.symm)
    hM_bd hβ_lo hβ_hi hF_nonpos
  have h1β : 1 - β = δ := by dsimp only [β]; ring
  have h12M : 12 * M = 2400 * (q : ℝ) := by dsimp only [M]; ring
  rwa [h1β, h12M] at hest

/-- **Zero-Free Segment → `L(1, χ)` Lower Bound**:
if `LFunction χ` has no real zero in `[1 - δ, 1)` (`0 < δ ≤ 1 / 4`), then
`δ / (4 * (2400 * q) ^ (6 * δ)) ≤ (LFunction χ 1).re`. -/
theorem LFunction_one_lower_bound_of_no_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hnozero : ∀ σ : ℝ, 1 - δ ≤ σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) :
    δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  apply LFunction_one_lower_bound_of_re_nonneg hχ hreal hδ0 hδ
  by_contra hneg; push Not at hneg
  have hpos1 : 0 < (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re := by
    simpa using (LFunction_one_pos_of_real χ hχ hreal).1
  have hcont : ContinuousOn (fun σ : ℝ => (DirichletCharacter.LFunction χ (σ : ℂ)).re)
      (Set.Icc (1 - δ) 1) :=
    (Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal)).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc
      (DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ)).re
      (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re :=
    ⟨hneg.le, hpos1.le⟩
  obtain ⟨β, hβ_mem, hβ_re⟩ := intermediate_value_Icc (by linarith : 1 - δ ≤ 1) hcont hmem
  have hβ_lt1 : β < 1 := lt_of_le_of_ne hβ_mem.2 fun h1 => by rw [h1] at hβ_re; linarith
  have hβ_pos : 0 < β := by linarith [hβ_mem.1]
  have hβ_im := LFunction_im_eq_zero_of_real hχ hreal hβ_pos
  have hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0 :=
    Complex.ext (by simpa using hβ_re) (by simpa using hβ_im)
  exact hnozero β hβ_mem.1 hβ_lt1 hzero

/-- **Contrapositive Real-Zero Existence**: if `(LFunction χ 1).re < δ / (4 * (2400 * q) ^ (6 * δ))`
for `δ ∈ (0, 1 / 4]`, then `LFunction χ` MUST have a real zero `β ∈ [1 - δ, 1)`. -/
theorem exists_real_zero_of_LFunction_one_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hlt : (DirichletCharacter.LFunction χ 1).re < δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ))) :
    ∃ β : ℝ, 1 - δ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
  by_contra hno
  push Not at hno
  have hge := LFunction_one_lower_bound_of_no_real_zero hχ hreal hδ0 hδ hno
  linarith

/-- **UNCONDITIONAL EFFECTIVE PAGE–LANDAU `L(1, χ) ≥ c / log Q` LOWER BOUND (AT MOST ONE EXCEPTION!)**:
there exists an explicit absolute constant `c > 0` such that for EVERY `Q ≥ 3`, there exists
`ψ₁ : PChar` such that for ALL `q ≤ Q` and ALL primitive real non-principal `χ : DirichletCharacter ℂ q`
with `PChar.of χ ≠ ψ₁`:
`c / Real.log (Q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re`. -/
theorem page_L1_lower_bound_all_but_one :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∃ ψ₁ : PChar,
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            q ≤ Q → χ.IsPrimitive → IsRealChar χ → χ ≠ 1 →
            PChar.of χ ≠ ψ₁ →
            c / Real.log (Q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re := by
  -- Use `Stage7SiegelWalfisz.page_landau_two_distinct_nonprincipal_real_explicit` (`1 / 3000`)!
  set c : ℝ := 1 / 500000
  refine ⟨c, by norm_num, fun Q hQ => ?_⟩
  have hQR : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  have hlog2Q_pos : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by linarith)
  have hlog2Q_le : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log (Q : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have hlog2 : Real.log (2 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set δ : ℝ := 1 / (6000 * Real.log (2 * (Q : ℝ)))
  have hδ0 : 0 < δ := by positivity
  have hlog6 : (1 : ℝ) < Real.log (2 * (Q : ℝ)) := by
    have h1 : Real.exp 1 < 2 * (Q : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h1)
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- Pairwise bound: any two distinct primitive real non-principal `χ₁, χ₂` cannot both fail
  have hpair : ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
      (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
      q₁ ≤ Q → q₂ ≤ Q → χ₁.IsPrimitive → χ₂.IsPrimitive →
      IsRealChar χ₁ → IsRealChar χ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      PChar.of χ₁ ≠ PChar.of χ₂ →
      ¬ ((DirichletCharacter.LFunction χ₁ 1).re < c / Real.log (Q : ℝ) ∧
         (DirichletCharacter.LFunction χ₂ 1).re < c / Real.log (Q : ℝ)) := by
    intro q₁ q₂ _ _ χ₁ χ₂ hq1 hq2 hprim1 hprim2 hreal1 hreal2 h1ne h2ne hne ⟨hlt1, hlt2⟩
    have hthresh : ∀ {q : ℕ} [NeZero q], q ≤ Q →
        c / Real.log (Q : ℝ) ≤ δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) := by
      intro q _ hq
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
      have hq_le : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq
      have h6δ_le : 6 * δ ≤ 1 / 1000 := by
        dsimp only [δ]
        have : 6 * (1 / (6000 * Real.log (2 * (Q : ℝ)))) = 1 / (1000 * Real.log (2 * (Q : ℝ))) := by ring
        rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have h2400 : (2400 : ℝ) ^ (6 * δ) ≤ 2 := by
        have h1 : (2400 : ℝ) ^ (6 * δ) ≤ (2400 : ℝ) ^ (1 / 1000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h6δ_le
        have h2 : (2400 : ℝ) ^ (1 / 1000 : ℝ) ≤ 2 := by
          have hpow : (2400 : ℝ) ≤ 2 ^ (1000 : ℝ) := by
            rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            have h12 : (2400 : ℝ) ≤ 2 ^ (12 : ℕ) := by norm_num
            exact h12.trans (pow_le_pow_right₀ (by norm_num) (by norm_num))
          have h3 := Real.rpow_le_rpow (by norm_num) hpow (by norm_num : (0 : ℝ) ≤ 1 / 1000)
          rw [← Real.rpow_mul (by norm_num)] at h3
          norm_num at h3
          exact h3
        exact h1.trans h2
      have hq_pow : (q : ℝ) ^ (6 * δ) ≤ 2 := by
        have h1 : (q : ℝ) ^ (6 * δ) ≤ (2 * (Q : ℝ)) ^ (6 * δ) :=
          Real.rpow_le_rpow hq_pos.le (by linarith) (by positivity)
        have h2 : (2 * (Q : ℝ)) ^ (6 * δ) = Real.exp (6 * δ * Real.log (2 * (Q : ℝ))) := by
          rw [Real.rpow_def_of_pos (by linarith), mul_comm]
        have h3 : 6 * δ * Real.log (2 * (Q : ℝ)) = 1 / 1000 := by
          dsimp only [δ]; field_simp [hlog2Q_pos.ne']; ring
        have h4 : Real.exp (1 / 1000 : ℝ) ≤ 2 := by
          have h5 := Real.exp_le_exp.mpr (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 2)
          have h6 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
        rw [h2, h3] at h1
        exact h1.trans h4
      have hprod : (2400 * (q : ℝ)) ^ (6 * δ) ≤ 4 := by
        rw [Real.mul_rpow (by norm_num) hq_pos.le]
        nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2400) (6 * δ),
          Real.rpow_nonneg hq_pos.le (6 * δ)]
      have hden_pos : 0 < 4 * (2400 * (q : ℝ)) ^ (6 * δ) := by positivity
      have h1 : δ / 16 ≤ δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) :=
        div_le_div_of_nonneg_left hδ0.le hden_pos (by linarith)
      have h2 : c / Real.log (Q : ℝ) ≤ δ / 16 := by
        dsimp only [c, δ]
        rw [show (1 / (6000 * Real.log (2 * (Q : ℝ)))) / 16 =
            1 / (96000 * Real.log (2 * (Q : ℝ))) by ring,
          show (1 / 500000 : ℝ) / Real.log (Q : ℝ) = 1 / (500000 * Real.log (Q : ℝ)) by ring]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      exact h2.trans h1
    obtain ⟨β₁, hβ₁_lo, _, hz1⟩ :=
      exists_real_zero_of_LFunction_one_lt h1ne hreal1 hδ0 hδ_le (hlt1.trans_le (hthresh hq1))
    obtain ⟨β₂, hβ₂_lo, _, hz2⟩ :=
      exists_real_zero_of_LFunction_one_lt h2ne hreal2 hδ0 hδ_le (hlt2.trans_le (hthresh hq2))
    have hpage := page_landau_two_distinct_nonprincipal_real_explicit (Q := (Q : ℝ)) (by linarith)
      (by exact_mod_cast hq1) (by exact_mod_cast hq2) hprim1 hprim2 h1ne h2ne hreal1 hreal2
      hne hz1 hz2
    have hmin_ge : 1 - δ ≤ min β₁ β₂ := le_min hβ₁_lo hβ₂_lo
    have hδ_lt : δ < 1 / (3000 * Real.log (2 * (Q : ℝ))) := by
      dsimp only [δ]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  -- Package pairwise exclusion into `∃ ψ₁, ∀ χ ≠ ψ₁, ...`
  by_cases hex : ∃ (q₀ : ℕ) (_ : NeZero q₀) (χ₀ : DirichletCharacter ℂ q₀),
      q₀ ≤ Q ∧ χ₀.IsPrimitive ∧ IsRealChar χ₀ ∧ χ₀ ≠ 1 ∧
      (DirichletCharacter.LFunction χ₀ 1).re < c / Real.log (Q : ℝ)
  · rcases hex with ⟨q₀, hne0, χ₀, hq0, hprim0, hreal0, hχ0ne, hlt0⟩
    refine ⟨PChar.of χ₀, fun q _ χ hq hprim hreal hχne hne => ?_⟩
    by_contra hlt; push Not at hlt
    exact hpair q₀ q χ₀ χ hq0 hq hprim0 hprim hreal0 hreal hχ0ne hχne hne.symm ⟨hlt0, hlt⟩
  · push Not at hex
    refine ⟨PChar.of (1 : DirichletCharacter ℂ 1), fun q hne χ hq hprim hreal hχne _ => ?_⟩
    exact hex q hne χ hq hprim hreal hχne

/-- **UNCONDITIONAL TWO-CHARACTER EFFECTIVE TATUZAWA THEOREM (EXPLICIT CONSTANT `ε / 100000`,
ALL CONDUCTORS `q₁, q₂ ≥ 2`, `0` ASSUMPTIONS!)**:
for EVERY `ε ∈ (0, 1 / 4)` and ANY TWO distinct primitive real non-principal Dirichlet characters
`χ₁ mod q₁`, `χ₂ mod q₂` (`PChar.of χ₁ ≠ PChar.of χ₂`), they CANNOT BOTH satisfy
`(LFunction χᵢ 1).re < (ε / 100000) / qᵢ ^ ε`! -/
theorem tatuzawa_two_char_effective_L1_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (hreal1 : IsRealChar χ₁) (hreal2 : IsRealChar χ₂)
    (h1ne : χ₁ ≠ 1) (h2ne : χ₂ ≠ 1)
    (hne : PChar.of χ₁ ≠ PChar.of χ₂) :
    ¬ ((DirichletCharacter.LFunction χ₁ 1).re < (ε / 100000) / (q₁ : ℝ) ^ ε ∧
       (DirichletCharacter.LFunction χ₂ 1).re < (ε / 100000) / (q₂ : ℝ) ^ ε) := by
  -- WLOG `q₁ ≤ q₂` via an inner symmetric lemma
  suffices hsym : ∀ {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
      {φ₁ : DirichletCharacter ℂ r₁} {φ₂ : DirichletCharacter ℂ r₂},
      r₁ ≤ r₂ → φ₁.IsPrimitive → φ₂.IsPrimitive →
      IsRealChar φ₁ → IsRealChar φ₂ → φ₁ ≠ 1 → φ₂ ≠ 1 →
      PChar.of φ₁ ≠ PChar.of φ₂ →
      ¬ ((DirichletCharacter.LFunction φ₁ 1).re < (ε / 100000) / (r₁ : ℝ) ^ ε ∧
         (DirichletCharacter.LFunction φ₂ 1).re < (ε / 100000) / (r₂ : ℝ) ^ ε) by
    rcases le_total q₁ q₂ with hle | hle
    · exact hsym hle hprim1 hprim2 hreal1 hreal2 h1ne h2ne hne
    · intro ⟨h1, h2⟩
      exact hsym hle hprim2 hprim1 hreal2 hreal1 h2ne h1ne hne.symm ⟨h2, h1⟩
  intro r₁ r₂ _ _ φ₁ φ₂ hr_le hprim1 hprim2 hreal1 hreal2 h1ne h2ne hne ⟨hlt1, hlt2⟩
  have hr1_ge2 : 2 ≤ r₁ := two_le_of_dirichletChar_ne_one h1ne
  have hr2_ge2 : 2 ≤ r₂ := two_le_of_dirichletChar_ne_one h2ne
  have hr1_R : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr1_ge2
  have hr2_R : (2 : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr2_ge2
  have hr_leR : (r₁ : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr_le
  -- Step 1: Set `η = ε / 24`, so both `φ₁` and `φ₂` must have real zeros `β₁, β₂ ∈ [1 - η, 1)`
  set η : ℝ := ε / 24
  have hη0 : 0 < η := by positivity
  have hη_le : η ≤ 1 / 4 := by dsimp only [η]; linarith
  have h6η_eq : 6 * η = ε / 4 := by dsimp only [η]; ring
  have hstep1 : ∀ {r : ℕ} [NeZero r], (2 : ℝ) ≤ (r : ℝ) →
      (ε / 100000) / (r : ℝ) ^ ε ≤ η / (4 * (2400 * (r : ℝ)) ^ (6 * η)) := by
    intro r _ hr
    have h2400 : (2400 : ℝ) ^ (6 * η) ≤ 50 := by
      have h1 : (2400 : ℝ) ^ (6 * η) ≤ (2400 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [h6η_eq]; linarith)
      have h2 : (2400 : ℝ) ^ (1 / 2 : ℝ) ≤ 50 := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact h1.trans h2
    have hr_pow : (r : ℝ) ^ (6 * η) ≤ (r : ℝ) ^ ε :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [h6η_eq]; linarith)
    have hprod : 4 * (2400 * (r : ℝ)) ^ (6 * η) ≤ 200 * (r : ℝ) ^ ε := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have h1 : (2400 : ℝ) ^ (6 * η) * (r : ℝ) ^ (6 * η) ≤ 50 * (r : ℝ) ^ ε :=
        mul_le_mul h2400 hr_pow (Real.rpow_nonneg (by linarith) _) (by norm_num)
      linarith
    have hden_pos : 0 < 4 * (2400 * (r : ℝ)) ^ (6 * η) := by positivity
    calc (ε / 100000) / (r : ℝ) ^ ε
        ≤ η / (200 * (r : ℝ) ^ ε) := by
          dsimp only [η]
          rw [show (ε / 24) / (200 * (r : ℝ) ^ ε) = (ε / 4800) / (r : ℝ) ^ ε by ring]
          exact div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
      _ ≤ η / (4 * (2400 * (r : ℝ)) ^ (6 * η)) :=
          div_le_div_of_nonneg_left hη0.le hden_pos hprod
  obtain ⟨β₁, hβ₁_lo, hβ₁_lt1, hz1⟩ :=
    exists_real_zero_of_LFunction_one_lt h1ne hreal1 hη0 hη_le (hlt1.trans_le (hstep1 hr1_R))
  obtain ⟨β₂, hβ₂_lo, hβ₂_lt1, hz2⟩ :=
    exists_real_zero_of_LFunction_one_lt h2ne hreal2 hη0 hη_le (hlt2.trans_le (hstep1 hr2_R))
  -- Step 2: Page–Landau two-character zero repulsion on `β = min β₁ β₂`
  set β : ℝ := min β₁ β₂
  have hβ_lo : 1 - η ≤ β := le_min hβ₁_lo hβ₂_lo
  have hβ_hi : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) hβ₁_lt1
  have hβ_ge34 : 3 / 4 ≤ β := by linarith
  have hpage := page_landau_two_distinct_nonprincipal_real_explicit (Q := (r₂ : ℝ)) hr2_R
    hr_leR le_rfl hprim1 hprim2 h1ne h2ne hreal1 hreal2 hne hz1 hz2
  have h1β_ge : 1 / (3000 * Real.log (2 * (r₂ : ℝ))) ≤ 1 - β := by linarith
  have h1β_le : 1 - β ≤ η := by linarith
  -- Step 3: 4-character Estermann bound at `β`!
  set ψ₁ : PChar := ⟨r₁, φ₁, hprim1⟩
  set ψ₂ : PChar := ⟨r₂, φ₂, hprim2⟩
  have hψ_ne : ψ₁ ≠ ψ₂ := by
    intro heq; apply hne
    rw [show PChar.of φ₁ = ψ₁ from PChar.of_self ψ₁,
      show PChar.of φ₂ = ψ₂ from PChar.of_self ψ₂, heq]
  have h12_ne : prodChar φ₁ φ₂ ≠ 1 :=
    prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
  have hreal12 : IsRealChar (prodChar φ₁ φ₂) := isRealChar_prodChar hreal1 hreal2
  set H : ℂ → ℂ := fun s =>
    DirichletCharacter.LFunction φ₁ s * DirichletCharacter.LFunction φ₂ s *
      DirichletCharacter.LFunction (prodChar φ₁ φ₂) s
  have hH_diff : Differentiable ℂ H :=
    ((DirichletCharacter.differentiable_LFunction h1ne).mul
      (DirichletCharacter.differentiable_LFunction h2ne)).mul
      (DirichletCharacter.differentiable_LFunction h12_ne)
  have hL1_pos := LFunction_one_pos_of_real φ₁ h1ne hreal1
  have hL2_pos := LFunction_one_pos_of_real φ₂ h2ne hreal2
  have hL12_pos := LFunction_one_pos_of_real (prodChar φ₁ φ₂) h12_ne hreal12
  set lam : ℝ :=
    (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
      (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re
  have hH1_eq : (lam : ℂ) = H 1 := by
    dsimp only [lam, H]
    have h1 : ((DirichletCharacter.LFunction φ₁ 1).re : ℂ) = DirichletCharacter.LFunction φ₁ 1 :=
      Complex.ext (by simp) (by simp [hL1_pos.2])
    have h2 : ((DirichletCharacter.LFunction φ₂ 1).re : ℂ) = DirichletCharacter.LFunction φ₂ 1 :=
      Complex.ext (by simp) (by simp [hL2_pos.2])
    have h3 : ((DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re : ℂ) =
        DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1 :=
      Complex.ext (by simp) (by simp [hL12_pos.2])
    push_cast; rw [h1, h2, h3]
  set F : ℂ → ℂ := fun s => riemannZeta s * H s
  set G : ℂ → ℂ := regZetaMul H
  set M : ℝ := 40000 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2
  have hM1 : 1 ≤ M := by
    have h4 : (4 : ℝ) ≤ (r₁ : ℝ) * (r₂ : ℝ) := by nlinarith
    dsimp only [M]; nlinarith
  have hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re} := differentiableOn_regZetaMul hH_diff
  have hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1) := by
    intro s hs hs1
    dsimp only [G, F]
    rw [regZetaMul_eq hs hs1, hH1_eq]
  have hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M := by
    intro s hs
    have hs_re : 0 < s.re := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have hre := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
      simp only [Complex.sub_re, Complex.re_ofNat] at hre; linarith
    have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have h := norm_add_le (s - 1) (-1)
      have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
      rw [h1, hs, norm_neg, norm_one] at h; linarith
    have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
    rw [hGF s hs_re hs1_ne]
    have hζ := norm_riemannZeta_le_of_mem_sphere hs
    have hL1 := norm_LFunction_le_of_mem_sphere h1ne hs
    have hL2 := norm_LFunction_le_of_mem_sphere h2ne hs
    have hL12 : ‖DirichletCharacter.LFunction (prodChar φ₁ φ₂) s‖ ≤ 15 * ((r₁ : ℝ) * (r₂ : ℝ)) := by
      simpa [Nat.cast_mul] using norm_LFunction_le_of_mem_sphere h12_ne hs
    have hHs : ‖H s‖ ≤ 3375 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      dsimp only [H]
      rw [norm_mul, norm_mul]
      have h1 : ‖DirichletCharacter.LFunction φ₁ s‖ * ‖DirichletCharacter.LFunction φ₂ s‖ ≤
          (15 * (r₁ : ℝ)) * (15 * (r₂ : ℝ)) :=
        mul_le_mul hL1 hL2 (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hL12 (norm_nonneg _) (by positivity)
      linarith
    have hH1_norm : ‖H 1‖ ≤ 216 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      dsimp only [H]
      rw [norm_mul, norm_mul]
      have hb1 : ‖DirichletCharacter.LFunction φ₁ 1‖ ≤ 6 * (r₁ : ℝ) := by
        have h := norm_LFunction_strip_le h1ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add] at h; linarith
      have hb2 : ‖DirichletCharacter.LFunction φ₂ 1‖ ≤ 6 * (r₂ : ℝ) := by
        have h := norm_LFunction_strip_le h2ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add] at h; linarith
      have hb12 : ‖DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1‖ ≤ 6 * ((r₁ : ℝ) * (r₂ : ℝ)) := by
        have h := norm_LFunction_strip_le h12_ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add, Nat.cast_mul] at h; nlinarith
      have h1 := mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hb12 (norm_nonneg _) (by positivity)
      linarith
    have hinv : ‖(lam : ℂ) / (s - 1)‖ ≤ 432 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      rw [hH1_eq, norm_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ‖riemannZeta s * H s - (lam : ℂ) / (s - 1)‖
        ≤ ‖riemannZeta s‖ * ‖H s‖ + ‖(lam : ℂ) / (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 10 * (3375 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2) + 432 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
          gcongr
      _ ≤ M := by dsimp only [M]; nlinarith
  have hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries (fourCharCoeff φ₁ φ₂) s := by
    intro s hs
    have h := (LSeries_fourCharCoeff_eq hreal1 hreal2 hs).2
    dsimp only [F, H]
    rw [h]; ring
  have hF_zero : (F (β : ℂ)).re ≤ 0 := by
    have h0 : F (β : ℂ) = 0 := by
      dsimp only [F, H, β]
      rcases min_choice β₁ β₂ with hβeq | hβeq
      · rw [hβeq, hz1]; ring
      · rw [hβeq, hz2]; ring
    rw [h0, Complex.zero_re]
  have hest := estermann_residue_lower_bound_of_nonpos
    (fourCharCoeff_zero φ₁ φ₂) (by rw [fourCharCoeff_one]) (fourCharCoeff_nonneg hreal1 hreal2)
    (fun x hx => (LSeries_fourCharCoeff_eq hreal1 hreal2 (by simpa using hx)).1)
    hM1 hG_diff hGF hagree hM_bd hβ_ge34 hβ_hi hF_zero
  -- Step 4: Numerical contradiction between lower bound `hest` and upper bound on `lam`!
  have h6_1β : 6 * (1 - β) ≤ ε / 4 := by linarith
  have h12M_le : (12 * M) ^ (6 * (1 - β)) ≤ 700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    have h12M_eq : 12 * M = 480000 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by dsimp only [M]; ring
    rw [h12M_eq, Real.mul_rpow (by norm_num) (by positivity)]
    have h480 : (480000 : ℝ) ^ (6 * (1 - β)) ≤ 700 := by
      have h1 : (480000 : ℝ) ^ (6 * (1 - β)) ≤ (480000 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h2 : (480000 : ℝ) ^ (1 / 2 : ℝ) ≤ 700 := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact h1.trans h2
    have hpow2 : (((r₁ : ℝ) * (r₂ : ℝ)) ^ 2) ^ (6 * (1 - β)) ≤ ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
      rw [← Real.rpow_natCast ((r₁ : ℝ) * (r₂ : ℝ)) 2, ← Real.rpow_mul (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
    exact mul_le_mul h480 hpow2 (Real.rpow_nonneg (by positivity) _) (by norm_num)
  have hlog2r2_pos : 0 < Real.log (2 * (r₂ : ℝ)) := Real.log_pos (by linarith)
  have hlam_lo :
      1 / (8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ≤ lam := by
    have hden_pos : 0 < 4 * (12 * M) ^ (6 * (1 - β)) := by positivity
    have h1 : (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) ≤
        (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) := by
      calc (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)))
          ≤ (1 - β) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) :=
            div_le_div_of_nonneg_right h1β_ge (by positivity)
        _ ≤ (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) :=
            div_le_div_of_nonneg_left (by linarith) hden_pos (by linarith)
    have h2 : (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) /
          (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) =
        1 / (8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) := by
      field_simp [hlog2r2_pos.ne', (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (r₁ : ℝ) * (r₂ : ℝ)) _).ne']
      ring
    rw [← h2]
    exact h1.trans hest
  -- Upper bound on `lam`: `L(1, φ₁ φ₂) ≤ 10 * log(2 r₂)`
  have hL12_up : (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re ≤ 10 * Real.log (2 * (r₂ : ℝ)) := by
    have hup := norm_LFunction_le_log_of_one_le_re h12_ne (s := 1) (by simp) (by simp)
    simp only [Complex.one_im, abs_zero, zero_add, Nat.cast_mul] at hup
    have hre : (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re ≤
        5 * Real.log ((r₁ : ℝ) * (r₂ : ℝ) * 2) :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hup
    have hlog_sq : Real.log ((r₁ : ℝ) * (r₂ : ℝ) * 2) ≤ 2 * Real.log (2 * (r₂ : ℝ)) := by
      have hsq : (r₁ : ℝ) * (r₂ : ℝ) * 2 ≤ (2 * (r₂ : ℝ)) ^ 2 := by nlinarith
      have h1 := Real.log_le_log (by positivity) hsq
      rw [Real.log_pow] at h1; push_cast at h1; exact h1
    linarith
  have hlam_up :
      lam < 10 * (ε / 100000) ^ 2 * Real.log (2 * (r₂ : ℝ)) / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε := by
    have hmul12 :
        (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re <
          ((ε / 100000) / (r₁ : ℝ) ^ ε) * ((ε / 100000) / (r₂ : ℝ) ^ ε) :=
      mul_lt_mul'' hlt1 hlt2 hL1_pos.1.le hL2_pos.1.le
    have hprod_eq :
        ((ε / 100000) / (r₁ : ℝ) ^ ε) * ((ε / 100000) / (r₂ : ℝ) ^ ε) =
          (ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε := by
      rw [Real.mul_rpow (by linarith) (by linarith)]
      ring
    rw [hprod_eq] at hmul12
    have h3 :
        (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
          (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re <
        ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) := by
      calc (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
              (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re
          ≤ (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
              (10 * Real.log (2 * (r₂ : ℝ))) :=
            mul_le_mul_of_nonneg_left hL12_up (mul_nonneg hL1_pos.1.le hL2_pos.1.le)
        _ < ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) :=
            mul_lt_mul_of_pos_right hmul12 (by positivity)
    dsimp only [lam]
    linarith [show ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) =
        10 * (ε / 100000) ^ 2 * Real.log (2 * (r₂ : ℝ)) / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε by ring]
  -- Bound `(log (2 * r₂)) ^ 2 ≤ (64 / ε ^ 2) * (r₁ * r₂) ^ (ε / 2)`
  have hlog_sq_bd : (Real.log (2 * (r₂ : ℝ))) ^ 2 ≤ (64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    have hlog1 : Real.log (2 * (r₂ : ℝ)) ≤ (2 * (r₂ : ℝ)) ^ (ε / 8) / (ε / 8) :=
      Real.log_le_rpow_div (by linarith) (by positivity)
    have h2r2_sq : 2 * (r₂ : ℝ) ≤ (r₂ : ℝ) ^ 2 := by nlinarith
    have hpow1 : (2 * (r₂ : ℝ)) ^ (ε / 8) ≤ (r₂ : ℝ) ^ (ε / 4) := by
      have h := Real.rpow_le_rpow (by linarith) h2r2_sq (by positivity : (0 : ℝ) ≤ ε / 8)
      rw [← Real.rpow_natCast (r₂ : ℝ) 2, ← Real.rpow_mul (by linarith)] at h
      have hexp : ((2 : ℕ) : ℝ) * (ε / 8) = ε / 4 := by push_cast; ring
      rwa [hexp] at h
    have hlog2 : Real.log (2 * (r₂ : ℝ)) ≤ (8 / ε) * (r₂ : ℝ) ^ (ε / 4) := by
      have h1 : (2 * (r₂ : ℝ)) ^ (ε / 8) / (ε / 8) = (8 / ε) * (2 * (r₂ : ℝ)) ^ (ε / 8) := by
        field_simp [hε0.ne']
      rw [h1] at hlog1
      exact hlog1.trans (mul_le_mul_of_nonneg_left hpow1 (by positivity))
    have hsq := pow_le_pow_left₀ hlog2r2_pos.le hlog2 2
    rw [mul_pow, ← Real.rpow_natCast ((r₂ : ℝ) ^ (ε / 4)) 2, ← Real.rpow_mul (by linarith)] at hsq
    have hexp2 : ε / 4 * ((2 : ℕ) : ℝ) = ε / 2 := by push_cast; ring
    rw [hexp2] at hsq
    have hr2_le_prod : (r₂ : ℝ) ^ (ε / 2) ≤ ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) :=
      Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
    calc (Real.log (2 * (r₂ : ℝ))) ^ 2
        ≤ (8 / ε) ^ 2 * (r₂ : ℝ) ^ (ε / 2) := hsq
      _ ≤ (8 / ε) ^ 2 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left hr2_le_prod (by positivity)
      _ = (64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by ring
  -- Combine `hlam_lo < hlam_up` and simplify to `1 < 0.5376`!
  have hcomb := hlam_lo.trans_lt hlam_up
  have hpow_pos : 0 < ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hpow_sq : ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε = (((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hpow_sq] at hcomb
  have hden1 : 0 < 8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by positivity
  have hden2 : 0 < (((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ^ 2 := sq_pos_of_pos hpow_pos
  have hcross := (div_lt_div_iff₀ hden1 hden2).mp hcomb
  -- Cancel one factor of `(r₁ * r₂) ^ (ε / 2)`
  have hcancel :
      ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) <
        84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2 := by
    nlinarith
  have hfinal :
      84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2 ≤
        (5376000000 / 100000 ^ 2 : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    calc 84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2
        ≤ 84000000 * (ε / 100000) ^ 2 * ((64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left hlog_sq_bd (by positivity)
      _ = (5376000000 / 100000 ^ 2 : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
          field_simp [hε0.ne']; ring
  nlinarith

/-- **UNCONDITIONAL TATUZAWA'S 1951 EFFECTIVE THEOREM (`0` ASSUMPTIONS, EXPLICIT CONSTANT
`ε / 100000`, AT MOST ONE EXCEPTION `ψ₁` ACROSS ALL CONDUCTORS `q ≥ 1`!)**:
for EVERY `ε ∈ (0, 1 / 4)`, there exists at most ONE primitive character `ψ₁ : PChar` such that
for ALL `q ≥ 1` (`[NeZero q]`) and ALL primitive real non-principal `χ : DirichletCharacter ℂ q`
with `PChar.of χ ≠ ψ₁`:
`(ε / 100000) / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re`. -/
theorem tatuzawa_effective_L1_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) :
    ∃ ψ₁ : PChar,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → IsRealChar χ → χ ≠ 1 →
        PChar.of χ ≠ ψ₁ →
        (ε / 100000) / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re := by
  by_cases hex : ∃ (q₀ : ℕ) (_ : NeZero q₀) (χ₀ : DirichletCharacter ℂ q₀),
      χ₀.IsPrimitive ∧ IsRealChar χ₀ ∧ χ₀ ≠ 1 ∧
      (DirichletCharacter.LFunction χ₀ 1).re < (ε / 100000) / (q₀ : ℝ) ^ ε
  · rcases hex with ⟨q₀, _, χ₀, hprim0, hreal0, hχ0ne, hlt0⟩
    refine ⟨PChar.of χ₀, fun q _ χ hprim hreal hχne hne => ?_⟩
    by_contra hlt; push Not at hlt
    exact tatuzawa_two_char_effective_L1_lower_bound hε0 hε hprim0 hprim hreal0 hreal
      hχ0ne hχne hne.symm ⟨hlt0, hlt⟩
  · push Not at hex
    refine ⟨PChar.of (1 : DirichletCharacter ℂ 1), fun q hne χ hprim hreal hχne _ => ?_⟩
    exact hex q hne χ hprim hreal hχne

private lemma LFunction_eq_of_pchar_eq {ψ₁ ψ₂ : PChar} (heq : ψ₁ = ψ₂) :
    ψ₁.N = ψ₂.N ∧ ∀ s : ℂ, DirichletCharacter.LFunction ψ₁.χ s = DirichletCharacter.LFunction ψ₂.χ s := by
  subst heq
  exact ⟨rfl, fun _ => rfl⟩

/-- Helper: if two primitive characters have the same `PChar.of`, their conductors and `L`-functions
agree identically. -/
private lemma LFunction_eq_of_pchar_of_eq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (heq : PChar.of χ₁ = PChar.of χ₂) :
    q₁ = q₂ ∧ ∀ s : ℂ, DirichletCharacter.LFunction χ₁ s = DirichletCharacter.LFunction χ₂ s := by
  set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
  set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
  have hψ : ψ₁ = ψ₂ := by
    rw [← PChar.of_self ψ₁, ← PChar.of_self ψ₂]
    exact heq
  exact LFunction_eq_of_pchar_eq hψ

/-- **FULL UNCONDITIONAL SIEGEL'S 1935 THEOREM (`0` EXCEPTIONS, `0` ASSUMPTIONS!)**:
for EVERY `ε > 0`, there exists `C > 0` such that for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY
primitive real non-principal Dirichlet character `χ : DirichletCharacter ℂ q` (`χ ^ 2 = 1`, `χ ≠ 1`):
`C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re`. -/
theorem siegel_theorem_L1_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re := by
  intro ε hε0
  set ε' : ℝ := min ε (1 / 8)
  have hε'0 : 0 < ε' := lt_min hε0 (by norm_num)
  have hε'lt : ε' < 1 / 4 := (min_le_right ε (1 / 8)).trans_lt (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left ε (1 / 8)
  obtain ⟨ψ₁, htat⟩ := tatuzawa_effective_L1_lower_bound hε'0 hε'lt
  by_cases hψ : ψ₁.IsReal ∧ ψ₁.χ ≠ 1
  · have hpos1 : 0 < (DirichletCharacter.LFunction ψ₁.χ 1).re :=
      (LFunction_one_pos_of_real ψ₁.χ hψ.2 hψ.1).1
    have hN1_pos : (0 : ℝ) < (ψ₁.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ₁.N)
    set v : ℝ := (DirichletCharacter.LFunction ψ₁.χ 1).re * (ψ₁.N : ℝ) ^ ε'
    have hv_pos : 0 < v := mul_pos hpos1 (Real.rpow_pos_of_pos hN1_pos ε')
    set C : ℝ := min (ε' / 100000) v
    have hC_pos : 0 < C := lt_min (by positivity) hv_pos
    refine ⟨C, hC_pos, fun q _ χ hprim hsq hχne => ?_⟩
    have hreal : IsRealChar χ := isRealChar_of_sq_eq_one hsq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hpow_le : (q : ℝ) ^ ε' ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hq1 hε'le
    by_cases hne : PChar.of χ ≠ ψ₁
    · have h1 := htat q χ hprim hreal hχne hne
      calc C / (q : ℝ) ^ ε
          ≤ (ε' / 100000) / (q : ℝ) ^ ε :=
            div_le_div_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ (ε' / 100000) / (q : ℝ) ^ ε' :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _) hpow_le
        _ ≤ (DirichletCharacter.LFunction χ 1).re := h1
    · push Not at hne
      have hof : PChar.of χ = PChar.of ψ₁.χ := by rwa [PChar.of_self ψ₁]
      obtain ⟨hqeq, hLeq⟩ := LFunction_eq_of_pchar_of_eq hprim ψ₁.prim hof
      calc C / (q : ℝ) ^ ε
          ≤ v / (q : ℝ) ^ ε :=
            div_le_div_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ v / (q : ℝ) ^ ε' :=
            div_le_div_of_nonneg_left hv_pos.le (Real.rpow_pos_of_pos (by linarith) _) hpow_le
        _ = (DirichletCharacter.LFunction ψ₁.χ 1).re := by
            dsimp only [v]
            rw [hqeq, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hN1_pos ε').ne']
        _ = (DirichletCharacter.LFunction χ 1).re := by rw [hLeq 1]
  · refine ⟨ε' / 100000, by positivity, fun q _ χ hprim hsq hχne => ?_⟩
    have hreal : IsRealChar χ := isRealChar_of_sq_eq_one hsq
    have hne : PChar.of χ ≠ ψ₁ := by
      intro heq
      have hof : PChar.of χ = PChar.of ψ₁.χ := by rwa [PChar.of_self ψ₁]
      set ψ : PChar := ⟨q, χ, hprim⟩
      have hψeq : ψ = ψ₁ := by rw [← PChar.of_self ψ]; exact heq
      subst hψeq
      exact hψ ⟨hreal, hχne⟩
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hpow_le : (q : ℝ) ^ ε' ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hq1 hε'le
    calc (ε' / 100000) / (q : ℝ) ^ ε
        ≤ (ε' / 100000) / (q : ℝ) ^ ε' :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _) hpow_le
      _ ≤ (DirichletCharacter.LFunction χ 1).re := htat q χ hprim hreal hχne hne

/-- **FULL UNCONDITIONAL SIEGEL REAL-ZERO EXCLUSION (`0` EXCEPTIONS!)**:
for EVERY `ε > 0`, there exists `C > 0` such that for EVERY primitive real non-principal
`χ : DirichletCharacter ℂ q` and EVERY real `β ≥ 1 - C / q ^ ε`:
`DirichletCharacter.LFunction χ (β : ℂ) ≠ 0`. -/
theorem siegel_real_zero_exclusion :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          ∀ β : ℝ, 1 - C / (q : ℝ) ^ ε ≤ β → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  intro ε hε0
  obtain ⟨C₁, hC₁, hsiegel⟩ := siegel_theorem_L1_lower_bound (ε / 2) (by positivity)
  -- Bound `288 * (log (2 * q)) ^ 2 ≤ K * q ^ (ε / 2)` for all `q ≥ 2`
  set K : ℝ := 288 * (8 / ε) ^ 2
  have hK_pos : 0 < K := by positivity
  set C : ℝ := C₁ / (2 * K)
  refine ⟨C, by positivity, fun q _ χ hprim hsq hχne β hβ hzero => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχne
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlow := hsiegel q χ hprim hsq hχne
  have hup := LFunction_one_le_mul_one_sub_zero hχne hzero
  have hlog_bd : Real.log (2 * (q : ℝ)) ≤ (8 / ε) * (q : ℝ) ^ (ε / 4) := by
    have h1 : Real.log (2 * (q : ℝ)) ≤ (2 * (q : ℝ)) ^ (ε / 8) / (ε / 8) :=
      Real.log_le_rpow_div (by linarith) (by positivity)
    have h2 : (2 * (q : ℝ)) ^ (ε / 8) ≤ (q : ℝ) ^ (ε / 4) := by
      have hsq2 : 2 * (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
      have h := Real.rpow_le_rpow (by linarith) hsq2 (by positivity : (0 : ℝ) ≤ ε / 8)
      rw [← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul (by linarith)] at h
      have hexp : ((2 : ℕ) : ℝ) * (ε / 8) = ε / 4 := by push_cast; ring
      rwa [hexp] at h
    have h3 : (2 * (q : ℝ)) ^ (ε / 8) / (ε / 8) = (8 / ε) * (2 * (q : ℝ)) ^ (ε / 8) := by
      field_simp [hε0.ne']
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hlog_sq : 288 * (Real.log (2 * (q : ℝ))) ^ 2 ≤ K * (q : ℝ) ^ (ε / 2) := by
    have hsq1 := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_bd 2
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (ε / 4)) 2, ← Real.rpow_mul (by linarith)] at hsq1
    have hexp : ε / 4 * ((2 : ℕ) : ℝ) = ε / 2 := by push_cast; ring
    rw [hexp] at hsq1
    dsimp only [K]; nlinarith
  have h1β : 1 - β ≤ C / (q : ℝ) ^ ε := by linarith
  have hpow_mul : (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ ε := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hmul : (1 - β) * (288 * (Real.log (2 * (q : ℝ))) ^ 2) ≤ (C₁ / 2) / (q : ℝ) ^ (ε / 2) := by
    have h1 : (1 - β) * (288 * (Real.log (2 * (q : ℝ))) ^ 2) ≤
        (C / (q : ℝ) ^ ε) * (K * (q : ℝ) ^ (ε / 2)) :=
      mul_le_mul h1β hlog_sq (by positivity) (by positivity)
    have h2 : (C / (q : ℝ) ^ ε) * (K * (q : ℝ) ^ (ε / 2)) = (C₁ / 2) / (q : ℝ) ^ (ε / 2) := by
      dsimp only [C]
      rw [← hpow_mul]
      have hpos : (q : ℝ) ^ (ε / 2) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      field_simp [hK_pos.ne', hpos]
    exact h1.trans_eq h2
  have hstrict : (C₁ / 2) / (q : ℝ) ^ (ε / 2) < C₁ / (q : ℝ) ^ (ε / 2) :=
    div_lt_div_of_pos_right (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  linarith

/-! ## Section 4: Unconditional Imaginary Quadratic Class-Number Lower Bounds (`h(-d)`) -/

/-- Number of roots of unity `w_d` in the imaginary quadratic field `ℚ(√(-d))`:
`6` for `d = 3`, `4` for `d = 4`, and `2` for all `d > 4`. -/
def wUnit (d : ℕ) : ℕ :=
  if d = 3 then 6 else if d = 4 then 4 else 2

theorem two_le_wUnit (d : ℕ) : 2 ≤ wUnit d := by
  unfold wUnit; split_ifs <;> norm_num

/-- **Dirichlet's Analytic Class Number `h(-d)`** for an odd real primitive character `χ mod d`:
`h(-d) = (w_d √d / (2 π)) * L(1, χ)`. -/
def analyticClassNumber {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) : ℝ :=
  ((wUnit d : ℝ) * Real.sqrt (d : ℝ) / (2 * Real.pi)) * (DirichletCharacter.LFunction χ 1).re

/-- Exact finite-sum evaluation of `analyticClassNumber χ` via `Stage6ClassNumberFormula`:
`h(-d) = -(w_d / (2 d)) * ∑_{a=1}^{d-1} a * (χ a).re`. -/
theorem analyticClassNumber_eq_neg_sum {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : IsRealChar χ) :
    analyticClassNumber χ =
      -((wUnit d : ℝ) / (2 * (d : ℝ))) *
        ∑ a ∈ Finset.Ico 1 d, (a : ℝ) * (χ (a : ZMod d)).re := by
  unfold analyticClassNumber
  rw [re_LFunction_one_eq_odd_real_primitive hprim hodd hreal]
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  field_simp [hd_pos.ne', hsqrt_pos.ne', hpi_pos.ne']

/-- Strict positivity of `analyticClassNumber χ` for every odd real primitive character `χ mod d`. -/
theorem analyticClassNumber_pos {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hodd : χ.Odd) (hreal : IsRealChar χ) :
    0 < analyticClassNumber χ := by
  unfold analyticClassNumber
  have hw : (0 : ℝ) < (wUnit d : ℝ) := by exact_mod_cast (by have := two_le_wUnit d; omega : 0 < wUnit d)
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hL := (LFunction_one_pos_of_real χ (ne_one_of_odd hodd) hreal).1
  exact mul_pos (div_pos (mul_pos hw (Real.sqrt_pos.mpr hd)) (by positivity)) hL

/-- Exact positive-integer integrality of `analyticClassNumber χ` for all odd conductors `d ≥ 5`,
directly from `Stage7SiegelWalfisz.dvd_sum_mul_odd_real_primitive`. -/
theorem analyticClassNumber_eq_natCast_of_odd {d : ℕ} [NeZero d] (hd_odd : Odd d) (hd5 : 5 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : IsRealChar χ) :
    ∃ h : ℕ, 1 ≤ h ∧ analyticClassNumber χ = (h : ℝ) := by
  have hw2 : wUnit d = 2 := by unfold wUnit; split_ifs <;> omega
  obtain ⟨k, hk⟩ := dvd_sum_mul_odd_real_primitive hd_odd hd5 hprim hreal
  have hneg := sum_mul_odd_real_primitive_le_neg_one hprim hodd hreal
  have hdZ : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr (NeZero.pos d)
  have hk_neg : k ≤ -1 := by nlinarith
  refine ⟨(-k).toNat, by omega, ?_⟩
  rw [analyticClassNumber_eq_neg_sum hprim hodd hreal, hw2, sum_mul_re_eq_intCast hreal, hk]
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hk_cast : (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := by
    have : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hk_cast]
  push_cast
  field_simp [hd_pos.ne']

/-- Lower-bound bridge: `analyticClassNumber χ ≥ (√d / π) * (LFunction χ 1).re` for EVERY `d`. -/
theorem sqrt_div_pi_mul_LFunction_le_analyticClassNumber {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hodd : χ.Odd) (hreal : IsRealChar χ) :
    (Real.sqrt (d : ℝ) / Real.pi) * (DirichletCharacter.LFunction χ 1).re ≤
      analyticClassNumber χ := by
  unfold analyticClassNumber
  have hw : (2 : ℝ) ≤ (wUnit d : ℝ) := by exact_mod_cast two_le_wUnit d
  have hL : 0 ≤ (DirichletCharacter.LFunction χ 1).re :=
    (LFunction_one_pos_of_real χ (ne_one_of_odd hodd) hreal).1.le
  have h1 : Real.sqrt (d : ℝ) / Real.pi ≤ (wUnit d : ℝ) * Real.sqrt (d : ℝ) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
    have hsp : 0 ≤ Real.sqrt (d : ℝ) * Real.pi := mul_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
    nlinarith
  exact mul_le_mul_of_nonneg_right h1 hL

/-- **UNCONDITIONAL EFFECTIVE TATUZAWA CLASS-NUMBER LOWER BOUND (EXPLICIT CONSTANT
`ε / (100000 * π)`, AT MOST ONE EXCEPTION!)**:
for EVERY `ε ∈ (0, 1 / 4)`, there exists at most ONE primitive character `ψ₁ : PChar` such that
for ALL `d ≥ 1` (`[NeZero d]`) and ALL odd real primitive `χ : DirichletCharacter ℂ d` with
`PChar.of χ ≠ ψ₁`:
`(ε / (100000 * Real.pi)) * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ`. -/
theorem classNumber_tatuzawa_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) :
    ∃ ψ₁ : PChar,
      ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
        χ.IsPrimitive → χ.Odd → IsRealChar χ →
        PChar.of χ ≠ ψ₁ →
        (ε / (100000 * Real.pi)) * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ := by
  obtain ⟨ψ₁, htat⟩ := tatuzawa_effective_L1_lower_bound hε0 hε
  refine ⟨ψ₁, fun d _ χ hprim hodd hreal hne => ?_⟩
  have hL := htat d χ hprim hreal (ne_one_of_odd hodd) hne
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hbridge := sqrt_div_pi_mul_LFunction_le_analyticClassNumber hodd hreal
  have hmul : (Real.sqrt (d : ℝ) / Real.pi) * ((ε / 100000) / (d : ℝ) ^ ε) ≤
      (Real.sqrt (d : ℝ) / Real.pi) * (DirichletCharacter.LFunction χ 1).re :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have hrew :
      (Real.sqrt (d : ℝ) / Real.pi) * ((ε / 100000) / (d : ℝ) ^ ε) =
        (ε / (100000 * Real.pi)) * (d : ℝ) ^ (1 / 2 - ε) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_sub hd_pos]
    ring
  rw [hrew] at hmul
  exact hmul.trans hbridge

/-- **UNCONDITIONAL EFFECTIVE PAGE CLASS-NUMBER LOWER BOUND (`h(-d) ≥ c √d / log D`, AT MOST ONE
EXCEPTION!)**. -/
theorem classNumber_page_lower_bound_all_but_one :
    ∃ c : ℝ, 0 < c ∧
      ∀ (D : ℕ), 3 ≤ D →
        ∃ ψ₁ : PChar,
          ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
            d ≤ D → χ.IsPrimitive → χ.Odd → IsRealChar χ →
            PChar.of χ ≠ ψ₁ →
            c * Real.sqrt (d : ℝ) / Real.log (D : ℝ) ≤ analyticClassNumber χ := by
  obtain ⟨c₀, hc₀, hpage⟩ := page_L1_lower_bound_all_but_one
  refine ⟨c₀ / Real.pi, by positivity, fun D hD => ?_⟩
  obtain ⟨ψ₁, hψ₁⟩ := hpage D hD
  refine ⟨ψ₁, fun d _ χ hd hprim hodd hreal hne => ?_⟩
  have hL := hψ₁ d χ hd hprim hreal (ne_one_of_odd hodd) hne
  have hbridge := sqrt_div_pi_mul_LFunction_le_analyticClassNumber hodd hreal
  have hmul := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ Real.sqrt (d : ℝ) / Real.pi)
  have hrew : (Real.sqrt (d : ℝ) / Real.pi) * (c₀ / Real.log (D : ℝ)) =
      (c₀ / Real.pi) * Real.sqrt (d : ℝ) / Real.log (D : ℝ) := by ring
  rw [hrew] at hmul
  exact hmul.trans hbridge

/-- **EFFECTIVE GAUSS CLASS-NUMBER GROWTH WITH AT MOST ONE EXCEPTION**:
for EVERY target height `H : ℝ`, there exist an **EXPLICIT** threshold `D₀` (independent of any
Siegel zero!) and at most ONE exception `ψ₁ : PChar` such that for ALL `d ≥ D₀` and ALL odd real
primitive `χ mod d` with `PChar.of χ ≠ ψ₁`, `H ≤ analyticClassNumber χ`. -/
theorem classNumber_tendsto_atTop_all_but_one :
    ∃ ψ₁ : PChar,
      ∀ H : ℝ,
        let D₀ : ℕ := Nat.ceil ((max H 1 * (800000 * Real.pi)) ^ 3) + 1
        ∀ (d : ℕ) [NeZero d], D₀ ≤ d →
          ∀ (χ : DirichletCharacter ℂ d),
            χ.IsPrimitive → χ.Odd → IsRealChar χ →
            PChar.of χ ≠ ψ₁ →
            H ≤ analyticClassNumber χ := by
  obtain ⟨ψ₁, htat⟩ := classNumber_tatuzawa_lower_bound (ε := 1 / 8) (by norm_num) (by norm_num)
  refine ⟨ψ₁, fun H => ?_⟩
  intro D₀ d _ hd χ hprim hodd hreal hne
  have hlow := htat d χ hprim hodd hreal hne
  have hcoeff : (1 / 8 : ℝ) / (100000 * Real.pi) = 1 / (800000 * Real.pi) := by ring
  have hexp : (1 / 2 : ℝ) - 1 / 8 = 3 / 8 := by norm_num
  rw [hcoeff, hexp] at hlow
  set A : ℝ := max H 1 * (800000 * Real.pi)
  have hA_pos : 0 < A := by positivity
  have hA3_le : A ^ 3 ≤ (d : ℝ) := by
    have h1 : A ^ 3 ≤ (Nat.ceil (A ^ 3) : ℝ) := Nat.le_ceil (A ^ 3)
    have h2 : (Nat.ceil (A ^ 3) : ℝ) ≤ (D₀ : ℝ) := by
      dsimp only [D₀]; exact_mod_cast Nat.le_succ _
    have h3 : (D₀ : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : 1 ≤ D₀ := by dsimp only [D₀]; omega
    exact_mod_cast this.trans hd
  have hpow_ge : A ≤ (d : ℝ) ^ (3 / 8 : ℝ) := by
    have h1 : A ≤ (d : ℝ) ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hA3_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast A 3, ← Real.rpow_mul hA_pos.le] at h
      norm_num at h
      exact h
    have h2 : (d : ℝ) ^ (1 / 3 : ℝ) ≤ (d : ℝ) ^ (3 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd_ge1 (by norm_num)
    exact h1.trans h2
  have hH_le : H ≤ (1 / (800000 * Real.pi)) * (d : ℝ) ^ (3 / 8 : ℝ) := by
    have h1 : H ≤ max H 1 := le_max_left H 1
    have h2 : max H 1 = (1 / (800000 * Real.pi)) * A := by
      dsimp only [A]; field_simp [Real.pi_pos.ne']
    have h3 : (1 / (800000 * Real.pi)) * A ≤ (1 / (800000 * Real.pi)) * (d : ℝ) ^ (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow_ge (by positivity)
    linarith
  exact hH_le.trans hlow

/-- **FULL UNCONDITIONAL HEILBRONN–SIEGEL CLASS-NUMBER LOWER BOUND (`0` EXCEPTIONS, `0`
ASSUMPTIONS!)**:
for EVERY `ε > 0`, there exists `C > 0` such that for EVERY `d ≥ 1` (`[NeZero d]`) and EVERY
odd real primitive character `χ : DirichletCharacter ℂ d`:
`C * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ`. -/
theorem heilbronn_siegel_classNumber_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
          χ.IsPrimitive → χ.Odd → IsRealChar χ →
          C * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ := by
  intro ε hε0
  obtain ⟨C₁, hC₁, hsiegel⟩ := siegel_theorem_L1_lower_bound ε hε0
  refine ⟨C₁ / Real.pi, by positivity, fun d _ χ hprim hodd hreal => ?_⟩
  have hL := hsiegel d χ hprim (isRealChar_sq_eq_one hreal) (ne_one_of_odd hodd)
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hbridge := sqrt_div_pi_mul_LFunction_le_analyticClassNumber hodd hreal
  have hmul := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ Real.sqrt (d : ℝ) / Real.pi)
  have hrew :
      (Real.sqrt (d : ℝ) / Real.pi) * (C₁ / (d : ℝ) ^ ε) =
        (C₁ / Real.pi) * (d : ℝ) ^ (1 / 2 - ε) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_sub hd_pos]
    ring
  rw [hrew] at hmul
  exact hmul.trans hbridge

/-- **FULL UNCONDITIONAL GAUSS CLASS-NUMBER PROBLEM (`h(-d) → ∞`, `0` EXCEPTIONS!)**:
for EVERY `H : ℝ`, there exists `D₀ : ℕ` such that for ALL `d ≥ D₀` and ALL odd real primitive
characters `χ : DirichletCharacter ℂ d`, `H ≤ analyticClassNumber χ`. -/
theorem gauss_classNumber_problem_unconditional :
    ∀ H : ℝ, ∃ D₀ : ℕ,
      ∀ (d : ℕ) [NeZero d], D₀ ≤ d →
        ∀ (χ : DirichletCharacter ℂ d),
          χ.IsPrimitive → χ.Odd → IsRealChar χ →
          H ≤ analyticClassNumber χ := by
  obtain ⟨C, hC, hhs⟩ := heilbronn_siegel_classNumber_lower_bound (1 / 4) (by norm_num)
  intro H
  set A : ℝ := max H 1 / C
  have hA_pos : 0 < A := by positivity
  refine ⟨Nat.ceil (A ^ 4) + 1, fun d _ hd χ hprim hodd hreal => ?_⟩
  have hlow := hhs d χ hprim hodd hreal
  have hexp : (1 / 2 : ℝ) - 1 / 4 = 1 / 4 := by norm_num
  rw [hexp] at hlow
  have hA4_le : A ^ 4 ≤ (d : ℝ) := by
    have h1 : A ^ 4 ≤ (Nat.ceil (A ^ 4) : ℝ) := Nat.le_ceil (A ^ 4)
    have h2 : (Nat.ceil (A ^ 4) : ℝ) ≤ ((Nat.ceil (A ^ 4) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ _
    have h3 : ((Nat.ceil (A ^ 4) + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow : A ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hA4_le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast A 4, ← Real.rpow_mul hA_pos.le] at h
    norm_num at h
    exact h
  have hH_le : H ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : H ≤ max H 1 := le_max_left H 1
    have h2 : max H 1 = C * A := by dsimp only [A]; field_simp [hC.ne']
    have h3 : C * A ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hpow hC.le
    linarith
  exact hH_le.trans hlow

/-- **Master Unconditional Stage 9 Theorem (Landau–Estermann–Tatuzawa–Siegel & Imaginary Quadratic
Class Numbers, `0` Assumptions!)**: simultaneously packaging:
1. Unconditional non-negativity & squares lower bound for `divisorCharSum` and `fourCharCoeff`,
2. Unconditional effective Page `L(1, χ) ≥ c / log Q` lower bound (at most 1 exception),
3. Unconditional explicit Tatuzawa `L(1, χ) ≥ (ε / 100000) / q ^ ε` lower bound (at most 1 exception),
4. Full unconditional Siegel's 1935 Theorem `L(1, χ) ≥ C(ε) / q ^ ε` (0 exceptions!),
5. Effective Tatuzawa class-number lower bound `h(-d) ≥ (ε / (100000 π)) d^{1/2 - ε}` (≤ 1 exception),
6. Full unconditional Heilbronn–Siegel `h(-d) ≥ C(ε) d^{1/2 - ε}` & Gauss class-number problem
   `h(-d) → ∞` (0 exceptions!). -/
theorem stage9_landauSiegel_unconditional :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), IsRealChar χ →
      (∀ n, 0 ≤ divisorCharSum χ n) ∧ (∀ m, 1 ≤ m → 1 ≤ divisorCharSum χ (m ^ 2))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∃ ψ₁ : PChar,
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            q ≤ Q → χ.IsPrimitive → IsRealChar χ → χ ≠ 1 → PChar.of χ ≠ ψ₁ →
            c / Real.log (Q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ ψ₁ : PChar,
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → IsRealChar χ → χ ≠ 1 → PChar.of χ ≠ ψ₁ →
          (ε / 100000) / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ ψ₁ : PChar,
        ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
          χ.IsPrimitive → χ.Odd → IsRealChar χ → PChar.of χ ≠ ψ₁ →
          (ε / (100000 * Real.pi)) * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
          χ.IsPrimitive → χ.Odd → IsRealChar χ →
          C * (d : ℝ) ^ (1 / 2 - ε) ≤ analyticClassNumber χ) ∧
    (∀ H : ℝ, ∃ D₀ : ℕ,
      ∀ (d : ℕ) [NeZero d], D₀ ≤ d →
        ∀ (χ : DirichletCharacter ℂ d),
          χ.IsPrimitive → χ.Odd → IsRealChar χ →
          H ≤ analyticClassNumber χ) :=
  ⟨fun _ _ _ hr => ⟨divisorCharSum_nonneg hr, fun _ hm => divisorCharSum_sq_ge_one hr hm⟩,
   page_L1_lower_bound_all_but_one,
   fun _ h0 h4 => tatuzawa_effective_L1_lower_bound h0 h4,
   siegel_theorem_L1_lower_bound,
   fun _ h0 h4 => classNumber_tatuzawa_lower_bound h0 h4,
   heilbronn_siegel_classNumber_lower_bound,
   gauss_classNumber_problem_unconditional⟩

end RHDirect.Stage9LandauSiegel
