import RHDirect.Stage7PNTInAP
import RHDirect.Stage7SiegelWalfisz
import RHDirect.Stage7SieveMethods
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage2DirichletAP
import RHDirect.ElementaryEquiv

/-!
# RHDirect.Stage8UniformAP

**UNCONDITIONAL PAGE'S UNIFORM PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS,
EFFECTIVE NON-EXCEPTIONAL DYADIC PRIME EXISTENCE & TITCHMARSH SHIFTED-PRIME DIVISOR BOUND**
(`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` warnings, `0` info) directly on Mathlib's
`DirichletCharacter.LFunction`, `Stage2DirichletAP.chebyshevPsiAP`, and `Nat.divisors` in pure
Mathlib `v4.33.1`.

## Main Contents
1. **Unconditional Uniform Zero-Free Region & Log-Derivative Bound Across ALL Non-Exceptional
   Moduli `q ≤ Q` (Section 1)**:
   - `norm_negLogDerivL_one_sub_negLogDerivZeta_le`: `‖(-L'/L)(1_q, s) - (-ζ'/ζ)(s)‖ ≤ log q`
     on `Re(s) > 1`.
   - `re_negLogDerivZeta_le_landau_all_im`: Landau bound on `Stage6EffectivePNT.zetaReg` yielding
     `Re(-ζ'/ζ)(σ + it) ≤ 8 log(8 (|t| + 2)² / δ²) + δ / (δ² + t²)` for ALL `t : ℝ` and
     `1 < σ ≤ 5 / 4` (`δ = σ - 1`).
   - `LFunction_real_char_nonreal_zeroFree`: uniform classical de la Vallée Poussin zero-free
     region `1 - 1 / (60000 * log (q * (|s.im| + 2))) ≤ s.re` for ALL non-real points `s.im ≠ 0`
     of EVERY non-principal real Dirichlet character `χ`.
   - `uniform_zeroFreeRegion_nonexceptional`: combines `LFunction_complex_char_deLaValleePoussin_zeroFree`,
     `LFunction_real_char_nonreal_zeroFree`, and `Stage7SiegelWalfisz.page_at_most_one_siegel_zero_unconditional`
     to obtain a uniform zero-free region `1 - c / log(Q (|s.im| + 2)) ≤ s.re` across ALL
     `q ≤ Q` avoiding at most ONE Page exceptional modulus `q₁`!
   - `uniform_negLogDerivL_nonexceptional_bound`: uniform Borel–Carathéodory log-derivative bound
     `‖(-L'/L)(s, χ)‖ ≤ C * (log (Q * (|s.im| + 2))) ^ 2` with absolute constants `c, C > 0`
     independent of `Q, q, χ, s`.
2. **Unconditional Page's Uniform PNT in Arithmetic Progressions (Section 2)**:
   - `uniform_psi1Char_bound_of_Q` & `uniform_chebyshevPsiChar_bound_of_Q`: uniform Perron
     contour shift (`Stage7PNTInAP.perron_contour_shift_psi1Char`) and complex finite-difference
     de-smoothing parameterized by `Q ≥ 2` (sharing the same exceptional modulus `q₁`).
   - `uniform_pnt_psiAP_of_Q`, `page_uniform_pnt_psiAP_sqrt`, and `page_uniform_pnt_psiAP`:
     completely unconditional (`0` assumptions!) uniform PNT in arithmetic progressions for
     `q ≤ exp(c (log x)^{1/20})` (and sharp `q ≤ exp(c √(log x))`) avoiding at most one
     exceptional modulus `q₁`!
3. **Effective Non-Exceptional Dyadic Prime Existence & Titchmarsh Divisor Upper Bound (Section 3)**:
   - `exists_prime_in_dyadic_ap_uniform_nonexceptional`: for all sufficiently large `x`, avoiding
     at most one exceptional modulus `q₁`, every `q ≤ exp(c (log x)^{1/20})` and `Nat.Coprime a q`
     admits a prime `p ∈ (x / 2, x]` with `p ≡ a [MOD q]`.
   - `sum_inv_totient_le`: `∑_{d=1}^M 1 / φ(d) ≤ 3 * (log M + 1)` via `Stage7SieveMethods.sum_divisors_squarefree_inv_totient`.
   - `titchmarsh_divisor_upper_bound_explicit` & `titchmarsh_divisor_upper_bound`:
     `∑_{p ≤ n, p prime} d(p - 1) ≤ 120 * n` for ALL `n : ℕ`, combining Dirichlet hyperbola
     splitting with `Stage7SieveMethods.brun_titchmarsh_ap`!
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage8UniformAP

/-! ## Section 1: Uniform Zero-Free Region & Log-Derivative Bound Across Non-Exceptional Moduli -/

/-- Finite geometric series bound for any prime `p`: `∑_{k=1}^K 1 / p^k ≤ 1 / (p - 1)`. -/
private lemma sum_inv_pow_prime_le_one {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((p : ℝ) ^ k)⁻¹ ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hsub_pos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have htel : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.Icc 1 K, ((p : ℝ) ^ k)⁻¹ =
      (p : ℝ)⁻¹ - ((p : ℝ) ^ (K + 1))⁻¹ := by
    induction K with
    | zero => simp
    | succ K ih =>
      have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), mul_add, ih]
      have hpow : (p : ℝ)⁻¹ * ((p : ℝ) ^ (K + 1))⁻¹ = ((p : ℝ) ^ (K + 2))⁻¹ := by
        rw [← mul_inv, mul_comm, ← pow_succ]
      linarith
  have hle : (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.Icc 1 K, ((p : ℝ) ^ k)⁻¹ ≤ (p : ℝ)⁻¹ := by
    rw [htel]
    have : (0 : ℝ) ≤ ((p : ℝ) ^ (K + 1))⁻¹ := by positivity
    linarith
  have heq : (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) - 1) := by
    field_simp [hp_pos.ne', (by linarith : (p : ℝ) - 1 ≠ 0)]
  have h1 : ∑ k ∈ Finset.Icc 1 K, ((p : ℝ) ^ k)⁻¹ ≤ 1 / ((p : ℝ) - 1) := by
    rw [← heq, le_div_iff₀ hsub_pos, mul_comm]
    exact hle
  have h2 : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  exact h1.trans h2

/-- Helper: `∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b` for nonnegative `f`. -/
private lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

/-- **Principal Character vs Riemann Zeta Log-Derivative Difference on `Re(s) > 1`**:
for every `q ≥ 1` (`[NeZero q]`) and every `s : ℂ` with `1 < s.re`:
`‖(-L'/L)(1_q, s) - (-ζ'/ζ)(s)‖ ≤ Real.log q`. -/
theorem norm_negLogDerivL_one_sub_negLogDerivZeta_le {q : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s -
        Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ Real.log (q : ℝ) := by
  rw [norm_sub_rev, Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs,
    Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs]
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum1 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) s :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs
  unfold LSeries
  rw [← Summable.tsum_sub hsumZ hsum1]
  have hsub_summ : Summable (fun n : ℕ =>
      LSeries.term (fun m => (Λ m : ℂ)) s n -
        LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n) :=
    Summable.sub hsumZ hsum1
  refine (norm_tsum_le_tsum_norm hsub_summ.norm).trans ?_
  refine Summable.tsum_le_of_sum_range_le hsub_summ.norm fun N => ?_
  have hq_pos : 0 < q := NeZero.pos q
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun m => (Λ m : ℂ)) s n -
          LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n‖ ≤
        if ¬ Nat.Coprime n q ∧ IsPrimePow n then Λ n / (n : ℝ) ^ s.re else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        Stage2DirichletAP.principal_char_apply_nat]
      by_cases hcop : Nat.Coprime n q
      · rw [if_pos hcop, one_mul, sub_self, norm_zero, if_neg (fun h => h.1 hcop)]
      · simp only [hcop, ↓reduceIte, zero_mul, zero_div, sub_zero, not_false_eq_true, true_and]
        by_cases hpp : IsPrimePow n
        · rw [if_pos hpp, norm_div, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
        · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
          simp [hpp, h0]
  have hsum_filt :
      ∑ n ∈ Finset.range N,
          ‖LSeries.term (fun m => (Λ m : ℂ)) s n -
            LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n‖ ≤
        ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n),
          Λ n / (n : ℝ) ^ s.re := by
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum fun n _ => hterm n
  have hsub :
      (Finset.range N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n) ⊆
        q.primeFactors.biUnion (fun p => (Finset.Icc 1 N).image (fun k => p ^ k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnN, hncop, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      exact hncop ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left k)
    have hk_le : k ≤ N := (le_of_lt (Nat.lt_pow_self hp.one_lt)).trans hnN.le
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq_pos.ne'⟩, k, ⟨hkpos, hk_le⟩, rfl⟩
  have hterm_nn : ∀ n : ℕ, 0 ≤ Λ n / (n : ℝ) ^ s.re := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hper_prime : ∀ p ∈ q.primeFactors,
      ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), Λ n / (n : ℝ) ^ s.re ≤ Real.log (p : ℝ) := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    calc ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), Λ n / (n : ℝ) ^ s.re
        ≤ ∑ k ∈ Finset.Icc 1 N, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s.re :=
          Finset.sum_image_le_of_nonneg fun _ _ => hterm_nn _
      _ ≤ ∑ k ∈ Finset.Icc 1 N, Real.log (p : ℝ) * ((p : ℝ) ^ k)⁻¹ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
            ArithmeticFunction.vonMangoldt_apply_prime hpr, Nat.cast_pow]
          have hpk_ge1 : (1 : ℝ) ≤ (p : ℝ) ^ k :=
            one_le_pow₀ (by exact_mod_cast hpr.one_lt.le)
          have hpow_le : (p : ℝ) ^ k ≤ ((p : ℝ) ^ k) ^ s.re := by
            conv_lhs => rw [← Real.rpow_one ((p : ℝ) ^ k)]
            exact Real.rpow_le_rpow_of_exponent_le hpk_ge1 hs.le
          have hpk_pos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hpr.pos) k
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hpk_pos hpow_le) (Real.log_natCast_nonneg p)
      _ = Real.log (p : ℝ) * ∑ k ∈ Finset.Icc 1 N, ((p : ℝ) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ Real.log (p : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (sum_inv_pow_prime_le_one hpr N) (Real.log_natCast_nonneg p)
      _ = Real.log (p : ℝ) := mul_one _
  have hsum_log : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    rw [← Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero,
      ← Nat.cast_prod]
    have hprod_pos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hprod_le : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hq_pos (Nat.prod_primeFactors_dvd q)
    exact Real.log_le_log hprod_pos hprod_le
  calc ∑ n ∈ Finset.range N,
          ‖LSeries.term (fun m => (Λ m : ℂ)) s n -
            LSeries.term (fun m => (1 : DirichletCharacter ℂ q) m * (Λ m : ℂ)) s n‖
      ≤ ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n),
          Λ n / (n : ℝ) ^ s.re := hsum_filt
    _ ≤ ∑ n ∈ q.primeFactors.biUnion (fun p => (Finset.Icc 1 N).image (fun k => p ^ k)),
          Λ n / (n : ℝ) ^ s.re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hterm_nn _
    _ ≤ ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), Λ n / (n : ℝ) ^ s.re :=
        sum_biUnion_le_nonneg _ _ _ hterm_nn
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := Finset.sum_le_sum hper_prime
    _ ≤ Real.log (q : ℝ) := hsum_log

/-- **All-Height Landau Upper Bound for `Re(-ζ'/ζ)(σ + it)`** on `1 < σ ≤ 5 / 4` (including
arbitrarily small `|t| > 0`, via `Stage6EffectivePNT.zetaReg`!):
setting `δ = σ - 1`,
`Re(-ζ'/ζ)(σ + it) ≤ 8 * log (8 * (|t| + 2)² / δ²) + δ / (δ² + t²)`. -/
theorem re_negLogDerivZeta_le_landau_all_im {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 5 / 4) :
    let δ : ℝ := σ - 1
    (Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
      8 * Real.log (8 * (|t| + 2) ^ 2 / δ ^ 2) + δ / (δ ^ 2 + t ^ 2) := by
  intro δ
  have hδ0 : 0 < δ := by dsimp only [δ]; linarith
  have hδ_le : δ ≤ 1 / 4 := by dsimp only [δ]; linarith
  set s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs_ne1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp [hs_re] at this; linarith
  have hs_an : AnalyticOnNhd ℂ Stage6EffectivePNT.zetaReg (Metric.closedBall s (1 / 2)) := by
    refine (Stage6EffectivePNT.differentiableOn_zetaReg.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz)
    rw [Complex.sub_re, hs_re] at hre_diff
    show 0 < z.re
    linarith
  have hs_nz : Stage6EffectivePNT.zetaReg s ≠ 0 := by
    rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta (by rw [hs_re]; linarith) hs_ne1]
    exact mul_ne_zero (sub_ne_zero.mpr hs_ne1)
      (riemannZeta_ne_zero_of_one_le_re (by rw [hs_re]; linarith))
  set M : ℝ := 8 * (|t| + 2) ^ 2 / δ ^ 2
  have hM_ge1 : 1 ≤ M := by
    dsimp only [M]
    rw [le_div_iff₀ (sq_pos_of_pos hδ0)]
    have : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hs_bd : ∀ z ∈ Metric.closedBall s (1 / 2),
      ‖Stage6EffectivePNT.zetaReg z‖ ≤ M * ‖Stage6EffectivePNT.zetaReg s‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s)).trans hz)
    rw [Complex.sub_re, hs_re] at hre_diff
    rw [Complex.sub_im, hs_im] at him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 2 := by linarith
    have hz_im_hi : |z.im| ≤ |t| + 1 / 2 := by
      have htri : |z.im| ≤ |t| + |z.im - t| := by
        simpa [add_sub_cancel] using abs_add_le t (z.im - t)
      linarith [abs_le.mpr him_diff]
    -- Bound `‖zetaReg z‖ ≤ 4 * (|t| + 2) ^ 2` directly from the Euler–Maclaurin formula
    have hz_norm : ‖z‖ ≤ |t| + 5 / 2 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith : 0 < z.re)] at h1
      linarith
    have hz1_norm : ‖z - 1‖ ≤ |t| + 2 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - 1)
      have hre1 : |(z - 1).re| ≤ 1 := by
        rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
      have him1 : |(z - 1).im| = |z.im| := by simp
      linarith
    have hint_le :
        ‖∫ u in Ioi (1 : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)‖ ≤ 2 := by
      have htail := Stage5ZetaZeroFree.norm_eulerMaclaurin_tail_le (a := 1) le_rfl (by linarith : 0 < z.re)
      rw [Real.one_rpow] at htail
      have hinv : 1 / z.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith : 0 < z.re)]; linarith
      exact htail.trans hinv
    have hreg_z : ‖Stage6EffectivePNT.zetaReg z‖ ≤ 4 * (|t| + 2) ^ 2 := by
      unfold Stage6EffectivePNT.zetaReg
      have hinner : ‖(1 : ℂ) - z * ∫ u in Ioi (1 : ℝ),
            ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)‖ ≤ 3 * (|t| + 2) := by
        have htri := norm_sub_le (1 : ℂ)
          (z * ∫ u in Ioi (1 : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))
        rw [norm_one, norm_mul] at htri
        have hmul : ‖z‖ * ‖∫ u in Ioi (1 : ℝ),
              ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)‖ ≤ 2 * (|t| + 5 / 2) := by
          have := mul_le_mul hz_norm hint_le (norm_nonneg _) (by linarith [abs_nonneg t])
          linarith
        linarith [abs_nonneg t]
      have htri := norm_add_le (1 : ℂ) ((z - 1) * (1 - z * ∫ u in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)))
      rw [norm_one, norm_mul] at htri
      have hprod : ‖z - 1‖ * ‖(1 : ℂ) - z * ∫ u in Ioi (1 : ℝ),
            ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)‖ ≤
          (|t| + 2) * (3 * (|t| + 2)) :=
        mul_le_mul hz1_norm hinner (norm_nonneg _) (by linarith [abs_nonneg t])
      have ht2 : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
      nlinarith
    -- Lower bound `‖zetaReg s‖ ≥ δ ^ 2 / 2`
    have hinv_s : ‖1 / Stage6EffectivePNT.zetaReg s‖ ≤ 2 / δ ^ 2 := by
      rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta (by rw [hs_re]; linarith) hs_ne1]
      rw [one_div, mul_inv, norm_mul, ← one_div, ← one_div]
      have hs1_ge : δ ≤ ‖s - 1‖ := by
        have h1 := Complex.abs_re_le_norm (s - 1)
        rw [Complex.sub_re, hs_re, Complex.one_re, abs_of_pos hδ0] at h1
        exact h1
      have hinv1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / δ := by
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hδ0 hs1_ge
      have hinv2 : ‖(1 : ℂ) / riemannZeta s‖ ≤ 2 / δ := by
        have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re hσ1 t
        have hle : σ / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ0.le
        exact (h.2.1.trans h.2.2).trans hle
      calc ‖(1 : ℂ) / (s - 1)‖ * ‖(1 : ℂ) / riemannZeta s‖
          ≤ (1 / δ) * (2 / δ) := mul_le_mul hinv1 hinv2 (norm_nonneg _) (by positivity)
        _ = 2 / δ ^ 2 := by rw [div_mul_div_comm, one_mul, sq]
    have h1 : ‖Stage6EffectivePNT.zetaReg z‖ / ‖Stage6EffectivePNT.zetaReg s‖ ≤ M := by
      rw [← norm_div, show Stage6EffectivePNT.zetaReg z / Stage6EffectivePNT.zetaReg s =
            Stage6EffectivePNT.zetaReg z * (1 / Stage6EffectivePNT.zetaReg s) by ring, norm_mul]
      calc ‖Stage6EffectivePNT.zetaReg z‖ * ‖1 / Stage6EffectivePNT.zetaReg s‖
          ≤ (4 * (|t| + 2) ^ 2) * (2 / δ ^ 2) :=
            mul_le_mul hreg_z hinv_s (norm_nonneg _) (by positivity)
        _ = M := by dsimp only [M]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs_nz)).mp h1
  have hs_zeros : ∀ ρ ∈ Metric.closedBall s (1 / 4),
      Stage6EffectivePNT.zetaReg ρ = 0 → ρ.re ≤ s.re := by
    intro ρ hρ hρ0
    by_contra hgt; push Not at hgt
    rw [hs_re] at hgt
    have hρ_ne1 : ρ ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta (by linarith) hρ_ne1] at hρ0
    exact (mul_ne_zero (sub_ne_zero.mpr hρ_ne1)
      (riemannZeta_ne_zero_of_one_le_re (by linarith))) hρ0
  have hlandau := Stage5ZetaZeroFree.landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM_ge1 hs_an hs_nz hs_bd hs_zeros
  have hreg_eq := Stage6EffectivePNT.negLogDerivZetaReg_eq_sub_pole
    (by rw [hs_re]; linarith) hs_ne1
    (riemannZeta_ne_zero_of_one_le_re (by rw [hs_re]; linarith))
  have hre_pole : (1 / (s - 1)).re = δ / (δ ^ 2 + t ^ 2) := by
    have hre1 : (s - 1).re = δ := by simp [s, δ]
    have him1 : (s - 1).im = t := by simp [s]
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hre1, him1]
    ring
  have hre_split : (Stage3ZeroFreeRegion.negLogDerivZeta s).re =
      (Stage6EffectivePNT.negLogDerivZetaReg s).re + (1 / (s - 1)).re := by
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    rw [hreg_eq, Complex.sub_re]; ring
  rw [hre_split, hre_pole]
  unfold Stage6EffectivePNT.negLogDerivZetaReg
  have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
  rw [h8] at hlandau
  linarith

/-- **UNCONDITIONAL UNIFORM DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR NON-REAL ZEROS OF REAL
DIRICHLET CHARACTERS (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY non-principal real character `χ : DirichletCharacter ℂ q`
(`χ ≠ 1`, `χ ^ 2 = 1`), and EVERY non-real point `s : ℂ` (`s.im ≠ 0`):
`1 - 1 / (60000 * Real.log (q * (|s.im| + 2))) ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0`. -/
theorem LFunction_real_char_nonreal_zeroFree {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {s : ℂ} (him : s.im ≠ 0)
    (hre : 1 - 1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hz
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ1
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlt1 : s.re < 1 := by
    by_contra hge; push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hge hz
  set γ : ℝ := s.im
  set β : ℝ := s.re
  set Q : ℝ := (q : ℝ) * (|γ| + 2)
  have hQ_ge4 : (4 : ℝ) ≤ Q := by dsimp only [Q]; nlinarith [abs_nonneg γ]
  set L : ℝ := Real.log Q
  have hL_gt1 : 1 < L := by
    have h4 : Real.exp 1 < Q := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  set δ : ℝ := 1 / (4000 * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 24 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlog48000 : Real.log (48000 : ℝ) < 16 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 48000) (by norm_num : (48000 : ℝ) ≤ 2 ^ 16)
    rw [Real.log_pow] at h1; norm_num at h1; linarith
  by_cases hγ : δ ≤ |γ|
  · -- Case 1: `|γ| ≥ δ` — apply 3-4-1 with `L(χ², s) = L(1_q, s)` bounded via `zetaReg`!
    set σ : ℝ := 1 + δ
    have hσ1 : 1 < σ := by linarith
    have hσ_le : σ ≤ 5 / 4 := by linarith
    -- Landau bound for `L(χ, ·)` on `closedBall s₁ (1 / 2)`
    set s₁ : ℂ := (σ : ℂ) + I * (γ : ℂ)
    have hs₁_re : s₁.re = σ := by simp [s₁]
    have hs₁_im : s₁.im = γ := by simp [s₁]
    have hs₁_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s₁ (1 / 2)) :=
      (DifferentiableOn.analyticOnNhd
        (fun z _ => (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ1)).differentiableWithinAt)
        isOpen_univ).mono (Set.subset_univ _)
    have hs₁_nz : DirichletCharacter.LFunction χ s₁ ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [hs₁_re]; linarith)
    set M₁ : ℝ := 12 * Q / δ
    have hM₁_ge1 : 1 ≤ M₁ := by dsimp only [M₁]; rw [le_div_iff₀ hδ_pos]; linarith
    have hs₁_bd : ∀ z ∈ Metric.closedBall s₁ (1 / 2),
        ‖DirichletCharacter.LFunction χ z‖ ≤ M₁ * ‖DirichletCharacter.LFunction χ s₁‖ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₁)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₁)).trans hz)
      rw [Complex.sub_re, hs₁_re] at hre_diff
      rw [Complex.sub_im, hs₁_im] at him_diff
      have hz_im_hi : |z.im| ≤ |γ| + 1 / 2 := by
        have htri : |z.im| ≤ |γ| + |z.im - γ| := by
          simpa [add_sub_cancel] using abs_add_le γ (z.im - γ)
        linarith [abs_le.mpr him_diff]
      have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * Q := by
        have h := Stage5ZetaZeroFree.norm_LFunction_strip_le hχ1
          (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
        dsimp only [Q]; nlinarith [abs_nonneg γ]
      have hinv_s₁ : ‖1 / DirichletCharacter.LFunction χ s₁‖ ≤ 2 / δ := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 γ).2.1
        have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
        rw [hσ_sub] at h
        exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
      have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ s₁‖ ≤ M₁ := by
        rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₁ =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₁) by ring, norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₁‖
            ≤ (6 * Q) * (2 / δ) := mul_le_mul hz_strip hinv_s₁ (norm_nonneg _) (by positivity)
          _ = M₁ := by dsimp only [M₁]; ring
      exact (div_le_iff₀ (norm_pos_iff.mpr hs₁_nz)).mp h1
    have hs₁_zeros : ∀ ρ ∈ Metric.closedBall s₁ (1 / 4),
        DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ s₁.re := by
      intro ρ _ hρ0
      by_contra hgt; push Not at hgt
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1)
        (by rw [hs₁_re] at hgt; linarith) hρ0
    have hs_mem : s ∈ Metric.closedBall s₁ (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : s - s₁ = (((β - σ : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      have h1 : 1 / (60000 * L) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      dsimp only [σ]; linarith
    have hlandau₁ := Stage5ZetaZeroFree.landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM₁_ge1 hs₁_an hs₁_nz hs₁_bd hs₁_zeros hs_mem hz
    have hs₁_sub_s : s₁ - s = (((σ - β : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
    have hre_inv : (1 / (s₁ - s)).re = 1 / (σ - β) := by
      rw [hs₁_sub_s, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    have hre_err : (s₁ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
      rw [hs₁_sub_s, Complex.ofReal_re, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
      have h1 : 1 / (60000 * L) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      dsimp only [σ]; linarith
    have hbound₁ : (Stage3ZeroFreeRegion.negLogDerivL χ s₁).re ≤
        8 * Real.log M₁ + 1 - 1 / (σ - β) := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      rw [hre_inv] at hlandau₁
      have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
      rw [h8] at hlandau₁
      linarith
    -- Bound `Re(-L'/L)(1_q, σ + 2iγ)` via `norm_negLogDerivL_one_sub_negLogDerivZeta_le` + `re_negLogDerivZeta_le_landau_all_im`
    set s₂ : ℂ := (σ : ℂ) + I * ((2 * γ : ℝ) : ℂ)
    have hs₂_re : 1 < s₂.re := by simp [s₂, hσ1]
    have hdiff_1q := norm_negLogDerivL_one_sub_negLogDerivZeta_le (q := q) hs₂_re
    have hre_1q_sub : (Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s₂).re -
        (Stage3ZeroFreeRegion.negLogDerivZeta s₂).re ≤ Real.log (q : ℝ) := by
      rw [← Complex.sub_re]
      exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hdiff_1q)
    have hlogq_le_L : Real.log (q : ℝ) ≤ L :=
      Real.log_le_log hq_pos (by dsimp only [Q]; nlinarith [abs_nonneg γ])
    have hzeta2 := re_negLogDerivZeta_le_landau_all_im (t := 2 * γ) hσ1 hσ_le
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rw [hσ_sub] at hzeta2
    have hpole : δ / (δ ^ 2 + (2 * γ) ^ 2) ≤ 1 / (5 * δ) := by
      have hsq : δ ^ 2 ≤ γ ^ 2 := by
        rw [← sq_abs γ]; exact pow_le_pow_left₀ hδ_pos.le hγ 2
      have hden : 5 * δ ^ 2 ≤ δ ^ 2 + (2 * γ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    set M₂ : ℝ := 8 * (|2 * γ| + 2) ^ 2 / δ ^ 2
    have hbound₂ : (Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) s₂).re ≤
        8 * Real.log M₂ + 1 / (5 * δ) + L := by
      dsimp only [s₂, M₂] at hre_1q_sub hzeta2 ⊢
      linarith
    -- Real-axis bound at `σ`
    have hbound₀ : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
      have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ1
      rwa [hσ_sub] at h
    -- Combine via 3-4-1
    have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_negLogDerivL_re_nonneg χ hσ1 γ
    rw [hχ2] at h341
    have h2it : (σ : ℂ) + 2 * I * (γ : ℂ) = s₂ := by dsimp only [s₂]; push_cast; ring
    rw [h2it] at h341
    -- Bound `log M₁ ≤ 16 + 2 * L` and `log M₂ ≤ 29 + 4 * L`
    have hL_le_Q : L ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hlogM₁ : Real.log M₁ ≤ 16 + 2 * L := by
      have hM₁_eq : M₁ = 48000 * Q * L := by dsimp only [M₁, δ]; field_simp [hL_pos.ne']; ring
      have hM₁_le : M₁ ≤ 48000 * Q ^ 2 := by rw [hM₁_eq]; nlinarith
      calc Real.log M₁ ≤ Real.log (48000 * Q ^ 2) := Real.log_le_log (by linarith) hM₁_le
        _ = Real.log (48000 : ℝ) + Real.log (Q ^ 2) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 16 + 2 * L := by linarith
    have hlogM₂ : Real.log M₂ ≤ 29 + 4 * L := by
      have h2γ_le : |2 * γ| + 2 ≤ Q := by
        rw [abs_mul, abs_of_pos two_pos]; dsimp only [Q]; nlinarith [abs_nonneg γ]
      have hsq_le : (|2 * γ| + 2) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by positivity) h2γ_le 2
      have hM₂_le : M₂ ≤ 128000000 * Q ^ 4 := by
        have hδ2 : 1 / δ ^ 2 = 16000000 * L ^ 2 := by
          dsimp only [δ]; field_simp [hL_pos.ne']; ring
        have h1 : M₂ = 8 * (|2 * γ| + 2) ^ 2 * (1 / δ ^ 2) := by dsimp only [M₂]; ring
        rw [h1, hδ2]
        have hL2 : L ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hL_pos.le hL_le_Q 2
        nlinarith [sq_nonneg Q]
      have hlog128 : Real.log (128000000 : ℝ) < 29 := by
        have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 128000000)
          (by norm_num : (128000000 : ℝ) ≤ 2 ^ 29)
        rw [Real.log_pow] at h1; norm_num at h1; linarith
      calc Real.log M₂ ≤ Real.log (128000000 * Q ^ 4) := Real.log_le_log (by positivity) hM₂_le
        _ = Real.log (128000000 : ℝ) + Real.log (Q ^ 4) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log (128000000 : ℝ) + 4 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 29 + 4 * L := by linarith
    have herr_strict : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ + L < 1 / (2 * δ) := by
      have h2000 : 2000 * L = 1 / (2 * δ) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
      nlinarith
    have hineq : 4 / (σ - β) < 37 / (10 * δ) := by
      have h4 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
      have h3 : 3 * (1 / δ) = 3 / δ := by ring
      have hcomb : 3 / δ + 1 / (5 * δ) + 1 / (2 * δ) = 37 / (10 * δ) := by
        field_simp [hδ_pos.ne']; ring
      linarith
    have hσβ_pos : 0 < σ - β := by linarith
    have hmul := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 10 * δ)).mp hineq
    have hβ_lt : β < 1 - 3 * δ / 37 := by dsimp only [σ] at hmul; linarith
    have hcmp : 1 / (60000 * L) < 3 * δ / 37 := by
      dsimp only [δ]
      rw [show 3 * (1 / (4000 * L)) / 37 = 3 / (148000 * L) by ring]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  · -- Case 2: `0 < |γ| < δ` — conjugate zero pair `{s, conj s}` + 2-character positivity at `σ = 1 + 3δ`!
    push Not at hγ
    set η : ℝ := 3 * δ
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 8 := by dsimp only [η]; linarith
    set σ : ℝ := 1 + η
    have hσ1 : 1 < σ := by linarith
    have hreal : Stage3ZeroFreeRegion.IsRealChar χ := Stage3ZeroFreeRegion.isRealChar_of_sq_eq_one hχ2
    have hinv : χ⁻¹ = χ := Stage3ZeroFreeRegion.isRealChar_inv_eq_self hreal
    have hz_conj : DirichletCharacter.LFunction χ (starRingEnd ℂ s) = 0 := by
      have h := (RHDirect.LFunction_eq_zero_conj_iff χ (.inl hχ1)).mpr hz
      rwa [hinv] at h
    have hne_conj : s ≠ starRingEnd ℂ s := by
      intro heq
      have := congrArg Complex.im heq
      simp only [Complex.conj_im] at this
      exact him (by linarith)
    have hσβ_le : σ - β ≤ 1 / 6 := by
      have h1 : 1 / (60000 * L) ≤ 1 / 60000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      dsimp only [σ]; linarith
    have hs_mem : s ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 := Complex.norm_le_abs_re_add_abs_im (s - (σ : ℂ))
      have hre1 : |(s - (σ : ℂ)).re| = σ - β := by
        simp only [Complex.sub_re, Complex.ofReal_re, β]; rw [abs_of_neg (by linarith)]; ring
      have him1 : |(s - (σ : ℂ)).im| = |γ| := by simp [γ]
      linarith
    have hs_conj_mem : starRingEnd ℂ s ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 := Complex.norm_le_abs_re_add_abs_im (starRingEnd ℂ s - (σ : ℂ))
      have hre1 : |(starRingEnd ℂ s - (σ : ℂ)).re| = σ - β := by
        simp only [Complex.sub_re, Complex.conj_re, Complex.ofReal_re, β]
        rw [abs_of_neg (by linarith)]; ring
      have him1 : |(starRingEnd ℂ s - (σ : ℂ)).im| = |γ| := by
        simp [γ, abs_neg]
      linarith
    -- Landau setup for `L(χ, ·)` on `closedBall (σ : ℂ) (1 / 2)`
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall (σ : ℂ) (1 / 2)) :=
      (DifferentiableOn.analyticOnNhd
        (fun z _ => (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ1)).differentiableWithinAt)
        isOpen_univ).mono (Set.subset_univ _)
    have hnz : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp [hσ1.le])
    set M₁ : ℝ := 12 * Q / η
    have hM₁_ge1 : 1 ≤ M₁ := by dsimp only [M₁]; rw [le_div_iff₀ hη_pos]; linarith
    have hbd : ∀ z ∈ Metric.closedBall (σ : ℂ) (1 / 2),
        ‖DirichletCharacter.LFunction χ z‖ ≤ M₁ * ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - (σ : ℂ))).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - (σ : ℂ))).trans hz)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero] at hre_diff him_diff
      have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * Q := by
        have h := Stage5ZetaZeroFree.norm_LFunction_strip_le hχ1
          (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
        have him_abs : |z.im| ≤ 1 / 2 := abs_le.mpr him_diff
        dsimp only [Q]; nlinarith [abs_nonneg γ]
      have hinv_s : ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ 2 / η := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 0).2.1
        simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
        have hσ_sub : σ - 1 = η := by dsimp only [σ]; ring
        rw [hσ_sub] at h
        exact h.trans (div_le_div_of_nonneg_right (by linarith) hη_pos.le)
      have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ M₁ := by
        rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ (σ : ℂ) =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ (σ : ℂ)) by ring, norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖
            ≤ (6 * Q) * (2 / η) := mul_le_mul hz_strip hinv_s (norm_nonneg _) (by positivity)
          _ = M₁ := by dsimp only [M₁]; ring
      exact (div_le_iff₀ (norm_pos_iff.mpr hnz)).mp h1
    have hzeros : ∀ ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4),
        DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ (σ : ℂ).re := by
      intro ρ _ hρ0
      by_contra hgt; push Not at hgt
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1)
        (by simp only [Complex.ofReal_re] at hgt; linarith) hρ0
    set S : Finset ℂ := {s, starRingEnd ℂ s}
    have hS : ∀ ρ ∈ S, ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4) ∧ DirichletCharacter.LFunction χ ρ = 0 := by
      intro ρ hρ
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hρ
      rcases hρ with rfl | rfl
      · exact ⟨hs_mem, hz⟩
      · exact ⟨hs_conj_mem, hz_conj⟩
    have hhalf : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
    have hlandau := Stage5ZetaZeroFree.landau_negLogDeriv_le_finset_zeros (R := 1 / 2) (M := M₁)
      (by norm_num) hM₁_ge1 han hnz hbd (by rw [hhalf]; exact hzeros) S (by rw [hhalf]; exact hS)
    have hsum_S : ∑ ρ ∈ S, (1 / ((σ : ℂ) - ρ)).re =
        2 * (σ - β) / ((σ - β) ^ 2 + γ ^ 2) := by
      dsimp only [S]
      rw [Finset.sum_pair hne_conj]
      have h1 : (1 / ((σ : ℂ) - s)).re = (σ - β) / ((σ - β) ^ 2 + γ ^ 2) := by
        rw [one_div, Complex.inv_re, Complex.normSq_apply]
        simp [β, γ]; ring
      have h2 : (1 / ((σ : ℂ) - starRingEnd ℂ s)).re = (σ - β) / ((σ - β) ^ 2 + γ ^ 2) := by
        rw [one_div, Complex.inv_re, Complex.normSq_apply]
        simp [β, γ]; ring
      rw [h1, h2]; ring
    rw [hsum_S] at hlandau
    have hbound_L : (Stage3ZeroFreeRegion.negLogDerivL χ (σ : ℂ)).re ≤
        8 * Real.log M₁ - (3 / 2) * (σ - β) / ((σ - β) ^ 2 + γ ^ 2) := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      have h8 : (4 : ℝ) / (1 / 2) = 8 := by norm_num
      rw [h8] at hlandau
      have h32 : (3 / 4 : ℝ) * (2 * (σ - β) / ((σ - β) ^ 2 + γ ^ 2)) =
          (3 / 2) * (σ - β) / ((σ - β) ^ 2 + γ ^ 2) := by ring
      linarith
    have hbound_Z : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / η + 1 := by
      have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ1
      have hσ_sub : σ - 1 = η := by dsimp only [σ]; ring
      rwa [hσ_sub] at h
    have hpos := Stage3ZeroFreeRegion.two_char_negLogDeriv_re_nonneg χ hσ1
    have hL_le_Q : L ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hlogM₁ : Real.log M₁ ≤ 16 + 2 * L := by
      have hM₁_le : M₁ ≤ 48000 * Q ^ 2 := by
        have h1 : M₁ = 16000 * Q * L := by dsimp only [M₁, η, δ]; field_simp [hL_pos.ne']; ring
        rw [h1]; nlinarith
      calc Real.log M₁ ≤ Real.log (48000 * Q ^ 2) := Real.log_le_log (by linarith) hM₁_le
        _ = Real.log (48000 : ℝ) + Real.log (Q ^ 2) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 16 + 2 * L := by linarith
    have herr : 1 + 8 * Real.log M₁ < 1 / (8 * η) := by
      have h4000 : (4000 / 24 : ℝ) * L = 1 / (8 * η) := by
        dsimp only [η, δ]; field_simp [hL_pos.ne']; ring
      nlinarith
    have hineq : (3 / 2) * (σ - β) / ((σ - β) ^ 2 + γ ^ 2) < 9 / (8 * η) := by
      have h98 : 1 / η + 1 / (8 * η) = 9 / (8 * η) := by field_simp [hη_pos.ne']; ring
      linarith
    -- Contradiction: `σ - β ∈ [η, 11/10 * η]` and `|γ| < η / 3` forces `(3/2)(σ-β)/((σ-β)² + γ²) > 9/(8η)`!
    have h1β : 1 - β ≤ η / 10 := by
      have h1 : 1 / (60000 * L) ≤ η / 10 := by
        dsimp only [η, δ]
        rw [show 3 * (1 / (4000 * L)) / 10 = 3 / (40000 * L) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      linarith
    have hu_lo : η ≤ σ - β := by dsimp only [σ]; linarith
    have hu_hi : σ - β ≤ (11 / 10 : ℝ) * η := by dsimp only [σ]; linarith
    have hγ_sq : γ ^ 2 < (η / 3) ^ 2 := by
      rw [← sq_abs γ]
      exact pow_lt_pow_left₀ (by dsimp only [η]; linarith) (abs_nonneg γ) (by norm_num)
    have hden_pos : 0 < (σ - β) ^ 2 + γ ^ 2 := by positivity
    have hmul := (div_lt_div_iff₀ hden_pos (by positivity : (0 : ℝ) < 8 * η)).mp hineq
    have hquad : 0 ≤ ((11 / 10 : ℝ) * η - (σ - β)) * (3 * (σ - β) - (7 / 10 : ℝ) * η) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- **UNCONDITIONAL UNIFORM ZERO-FREE REGION ACROSS ALL NON-EXCEPTIONAL MODULI `q ≤ Q`**
(`0` assumptions!):
there exists an absolute constant `c > 0` such that for EVERY `Q ≥ 2`, there exists at most ONE
exceptional modulus `q₁ : ℕ` (`q₁ = 0 ∨ 2 ≤ q₁ ≤ Q`) such that for EVERY `q ≤ Q` (`[NeZero q]`)
with `q₁ = 0 ∨ ¬ q₁ ∣ q`, EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`), and EVERY
`s : ℂ` with `1 - c / Real.log (Q * (|s.im| + 2)) ≤ s.re`:
`DirichletCharacter.LFunction χ s ≠ 0`. -/
theorem uniform_zeroFreeRegion_nonexceptional :
    ∃ c : ℝ, 0 < c ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ s : ℂ, 1 - c / Real.log (Q * (|s.im| + 2)) ≤ s.re →
                DirichletCharacter.LFunction χ s ≠ 0 := by
  classical
  obtain ⟨c_P, hc_P, hreal_ne, huniq⟩ := Stage7SiegelWalfisz.page_at_most_one_siegel_zero_unconditional
  set c : ℝ := min (c_P / 2) (1 / 60000) with hc_def
  have hc_pos : 0 < c := lt_min (by positivity) (by norm_num)
  have hc_le_P : c ≤ c_P / 2 := min_le_left _ _
  have hc_le_60k : c ≤ 1 / 60000 := min_le_right _ _
  refine ⟨c, hc_pos, fun Q hQ => ?_⟩
  set Q_nat : ℕ := ⌊Q⌋₊
  have hQ_nat_ge2 : 2 ≤ Q_nat := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hQ)
  have hQ_nat_le : (Q_nat : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hL2Q_pos : 0 < Real.log (2 * (Q_nat : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Q_nat))
  by_cases hex : ∃ (ψ : PChar) (β : ℝ), ψ.N ≤ Q_nat ∧
      DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 ∧
      1 - c_P / Real.log (2 * (Q_nat : ℝ)) < β
  · obtain ⟨ψ₁, β₁, hN₁, hz₁, hβ₁⟩ := hex
    obtain ⟨_, hψ₁_ne1⟩ := hreal_ne Q_nat hQ_nat_ge2 ψ₁ β₁ hN₁ hz₁ hβ₁
    have hq₁_ge2 : 2 ≤ ψ₁.N := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hψ₁_ne1
    refine ⟨ψ₁.N, Or.inr ⟨hq₁_ge2, (by exact_mod_cast hN₁ : (ψ₁.N : ℝ) ≤ (Q_nat : ℝ)).trans hQ_nat_le⟩,
      fun q _ hqQ hndvd χ hχ s hs => ?_⟩
    have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hq_le_Qnat : q ≤ Q_nat := (Nat.le_floor_iff (by linarith)).mpr hqQ
    have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_pos (by nlinarith [abs_nonneg s.im])
    have hlogQ_ge : Real.log ((q : ℝ) * (|s.im| + 2)) ≤ Real.log (Q * (|s.im| + 2)) :=
      Real.log_le_log (by have : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q); positivity)
        (mul_le_mul_of_nonneg_right hqQ (by linarith [abs_nonneg s.im]))
    have hlogQ_pos : 0 < Real.log (Q * (|s.im| + 2)) := hlogq_pos.trans_le hlogQ_ge
    by_cases hχ2 : χ ^ 2 ≠ 1
    · refine Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ hχ2 ?_
      have h1 : c / Real.log (Q * (|s.im| + 2)) ≤
          1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
        calc c / Real.log (Q * (|s.im| + 2))
            ≤ (1 / 14000 : ℝ) / Real.log (Q * (|s.im| + 2)) :=
              div_le_div_of_nonneg_right (hc_le_60k.trans (by norm_num)) hlogQ_pos.le
          _ ≤ (1 / 14000 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) :=
              div_le_div_of_nonneg_left (by norm_num) hlogq_pos hlogQ_ge
          _ = 1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by ring
      linarith
    · push Not at hχ2
      by_cases him : s.im ≠ 0
      · refine LFunction_real_char_nonreal_zeroFree hχ hχ2 him ?_
        have h1 : c / Real.log (Q * (|s.im| + 2)) ≤
            1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
          calc c / Real.log (Q * (|s.im| + 2))
              ≤ (1 / 60000 : ℝ) / Real.log (Q * (|s.im| + 2)) :=
                div_le_div_of_nonneg_right hc_le_60k hlogQ_pos.le
            _ ≤ (1 / 60000 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) :=
                div_le_div_of_nonneg_left (by norm_num) hlogq_pos hlogQ_ge
            _ = 1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by ring
        linarith
      · push Not at him
        intro hz
        have hs_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
        have hlog4 : (1 : ℝ) < Real.log (Q * (|s.im| + 2)) := by
          have : Real.exp 1 < Q * (|s.im| + 2) := by
            have := Real.exp_one_lt_d9; nlinarith [abs_nonneg s.im]
          exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
        have hs_re_pos : 0 < s.re := by
          have h1 : c / Real.log (Q * (|s.im| + 2)) ≤ 1 / 60000 := by
            calc c / Real.log (Q * (|s.im| + 2)) ≤ (1 / 60000) / 1 :=
                  div_le_div₀ (by norm_num) hc_le_60k zero_lt_one hlog4.le
              _ = 1 / 60000 := div_one _
          linarith
        have hz_prim : DirichletCharacter.LFunction (PChar.of χ).χ (s.re : ℂ) = 0 := by
          rw [hs_eq] at hz
          exact (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ
            (by simpa using hs_re_pos) (.inl hχ)).mp hz
        have hcond_le : (PChar.of χ).N ≤ Q_nat :=
          (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hq_le_Qnat
        have hlog_cmp : Real.log (2 * (Q_nat : ℝ)) ≤ Real.log (Q * (|s.im| + 2)) := by
          rw [him, abs_zero, zero_add]
          exact Real.log_le_log (by positivity) (by linarith)
        have hs_gt : 1 - c_P / Real.log (2 * (Q_nat : ℝ)) < s.re := by
          have h1 : c / Real.log (Q * (|s.im| + 2)) < c_P / Real.log (2 * (Q_nat : ℝ)) := by
            calc c / Real.log (Q * (|s.im| + 2))
                ≤ (c_P / 2) / Real.log (Q * (|s.im| + 2)) :=
                  div_le_div_of_nonneg_right hc_le_P hlogQ_pos.le
              _ ≤ (c_P / 2) / Real.log (2 * (Q_nat : ℝ)) :=
                  div_le_div_of_nonneg_left (by positivity) hL2Q_pos hlog_cmp
              _ < c_P / Real.log (2 * (Q_nat : ℝ)) :=
                  div_lt_div_of_pos_right (by linarith) hL2Q_pos
          linarith
        have heq_ψ : PChar.of χ = ψ₁ :=
          (huniq Q_nat hQ_nat_ge2 (PChar.of χ) ψ₁ s.re β₁ hcond_le hN₁ hz_prim hz₁ hs_gt hβ₁).1
        have hdvd : ψ₁.N ∣ q := by
          have hN_eq : (PChar.of χ).N = ψ₁.N := congrArg PChar.N heq_ψ
          rw [← hN_eq]
          exact χ.conductor_dvd_level
        rcases hndvd with h0 | hnd
        · omega
        · exact hnd hdvd
  · refine ⟨0, Or.inl rfl, fun q _ hqQ _ χ hχ s hs => ?_⟩
    have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hq_le_Qnat : q ≤ Q_nat := (Nat.le_floor_iff (by linarith)).mpr hqQ
    have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
      Real.log_pos (by nlinarith [abs_nonneg s.im])
    have hlogQ_ge : Real.log ((q : ℝ) * (|s.im| + 2)) ≤ Real.log (Q * (|s.im| + 2)) :=
      Real.log_le_log (by have : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q); positivity)
        (mul_le_mul_of_nonneg_right hqQ (by linarith [abs_nonneg s.im]))
    have hlogQ_pos : 0 < Real.log (Q * (|s.im| + 2)) := hlogq_pos.trans_le hlogQ_ge
    by_cases hχ2 : χ ^ 2 ≠ 1
    · refine Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ hχ2 ?_
      have h1 : c / Real.log (Q * (|s.im| + 2)) ≤
          1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
        calc c / Real.log (Q * (|s.im| + 2))
            ≤ (1 / 14000 : ℝ) / Real.log (Q * (|s.im| + 2)) :=
              div_le_div_of_nonneg_right (hc_le_60k.trans (by norm_num)) hlogQ_pos.le
          _ ≤ (1 / 14000 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) :=
              div_le_div_of_nonneg_left (by norm_num) hlogq_pos hlogQ_ge
          _ = 1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by ring
      linarith
    · push Not at hχ2
      by_cases him : s.im ≠ 0
      · refine LFunction_real_char_nonreal_zeroFree hχ hχ2 him ?_
        have h1 : c / Real.log (Q * (|s.im| + 2)) ≤
            1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
          calc c / Real.log (Q * (|s.im| + 2))
              ≤ (1 / 60000 : ℝ) / Real.log (Q * (|s.im| + 2)) :=
                div_le_div_of_nonneg_right hc_le_60k hlogQ_pos.le
            _ ≤ (1 / 60000 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) :=
                div_le_div_of_nonneg_left (by norm_num) hlogq_pos hlogQ_ge
            _ = 1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by ring
        linarith
      · push Not at him
        intro hz
        have hs_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
        have hlog4 : (1 : ℝ) < Real.log (Q * (|s.im| + 2)) := by
          have : Real.exp 1 < Q * (|s.im| + 2) := by
            have := Real.exp_one_lt_d9; nlinarith [abs_nonneg s.im]
          exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
        have hs_re_pos : 0 < s.re := by
          have h1 : c / Real.log (Q * (|s.im| + 2)) ≤ 1 / 60000 := by
            calc c / Real.log (Q * (|s.im| + 2)) ≤ (1 / 60000) / 1 :=
                  div_le_div₀ (by norm_num) hc_le_60k zero_lt_one hlog4.le
              _ = 1 / 60000 := div_one _
          linarith
        have hz_prim : DirichletCharacter.LFunction (PChar.of χ).χ (s.re : ℂ) = 0 := by
          rw [hs_eq] at hz
          exact (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ
            (by simpa using hs_re_pos) (.inl hχ)).mp hz
        have hcond_le : (PChar.of χ).N ≤ Q_nat :=
          (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hq_le_Qnat
        have hlog_cmp : Real.log (2 * (Q_nat : ℝ)) ≤ Real.log (Q * (|s.im| + 2)) := by
          rw [him, abs_zero, zero_add]
          exact Real.log_le_log (by positivity) (by linarith)
        have hs_gt : 1 - c_P / Real.log (2 * (Q_nat : ℝ)) < s.re := by
          have h1 : c / Real.log (Q * (|s.im| + 2)) < c_P / Real.log (2 * (Q_nat : ℝ)) := by
            calc c / Real.log (Q * (|s.im| + 2))
                ≤ (c_P / 2) / Real.log (Q * (|s.im| + 2)) :=
                  div_le_div_of_nonneg_right hc_le_P hlogQ_pos.le
              _ ≤ (c_P / 2) / Real.log (2 * (Q_nat : ℝ)) :=
                  div_le_div_of_nonneg_left (by positivity) hL2Q_pos hlog_cmp
              _ < c_P / Real.log (2 * (Q_nat : ℝ)) :=
                  div_lt_div_of_pos_right (by linarith) hL2Q_pos
          linarith
        exact hex ⟨PChar.of χ, s.re, hcond_le, hz_prim, hs_gt⟩

/-- **UNCONDITIONAL UNIFORM-IN-`q` LOG-DERIVATIVE BOUND ACROSS ALL NON-EXCEPTIONAL MODULI `q ≤ Q`**
(`0` assumptions!):
there exist absolute constants `c' > 0` and `C' > 0` (independent of `Q, q, χ, s`) such that for
EVERY `Q ≥ 2`, there exists `q₁ : ℕ` (`q₁ = 0 ∨ 2 ≤ q₁ ≤ Q`) such that for EVERY `q ≤ Q`
(`[NeZero q]`) with `q₁ = 0 ∨ ¬ q₁ ∣ q`, EVERY non-principal `χ : DirichletCharacter ℂ q`
(`χ ≠ 1`), and EVERY `s : ℂ` with `1 - c' / Real.log (Q * (|s.im| + 2)) ≤ s.re ≤ 2`:
`LFunction χ s ≠ 0` and `‖(-L'/L)(s, χ)‖ ≤ C' * (Real.log (Q * (|s.im| + 2))) ^ 2`. -/
theorem uniform_negLogDerivL_nonexceptional_bound :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ s : ℂ, 1 - c' / Real.log (Q * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
                DirichletCharacter.LFunction χ s ≠ 0 ∧
                ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
                  C' * (Real.log (Q * (|s.im| + 2))) ^ 2 := by
  obtain ⟨c_zf, hc_zf_pos, hzf_all⟩ := uniform_zeroFreeRegion_nonexceptional
  set c : ℝ := min c_zf (1 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc_zf_pos (by norm_num)
  have hc_le_zf : c ≤ c_zf := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  set c' : ℝ := c / 32 with hc'_def
  have hc'_pos : 0 < c' := by positivity
  set C_right : ℝ := 1 / c' + 1 with hC_right_def
  have h128_gt1 : (1 : ℝ) < 128 / c := by rw [one_lt_div hc_pos]; linarith
  have hlog128_pos : 0 < Real.log (128 / c) := Real.log_pos h128_gt1
  set A_M : ℝ := Real.log (128 / c) + 2 with hAM_def
  have hAM_pos : 0 < A_M := by positivity
  set C_left : ℝ := (32 / c) * A_M with hC_left_def
  have hC_left_pos : 0 < C_left := by positivity
  set C' : ℝ := max C_right C_left with hC'_def
  have hC'_pos : 0 < C' := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c', hc'_pos, C', hC'_pos, fun Q hQ => ?_⟩
  obtain ⟨q₁, hq₁_spec, hzf⟩ := hzf_all Q hQ
  refine ⟨q₁, hq₁_spec, fun q _ hqQ hndvd χ hχ s hre_lo hre_hi => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (Q * (|t| + 2)) with hL_def
  have hQt_ge4 : (4 : ℝ) ≤ Q * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hL_gt1 : 1 < L := by
    have : Real.exp 1 < Q * (|t| + 2) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  have hsnz : DirichletCharacter.LFunction χ s ≠ 0 := by
    refine hzf q hqQ hndvd χ hχ s ?_
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
      exact hzf q hqQ hndvd χ hχ z (by dsimp only [R_open] at hre_diff; linarith)
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
      have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
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
        have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
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

/-! ## Section 2: Unconditional Page's Uniform PNT in Arithmetic Progressions (`0` Assumptions!) -/

/-- Elementary exponential decay inequality: `u ^ 2 * exp (-2 * u) ≤ 1` for `u ≥ 0`. -/
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

/-- **UNCONDITIONAL UNIFORM-IN-`q` PERRON BOUND FOR NON-PRINCIPAL `ψ₁(y, χ)` (`Q`-PARAMETERIZED)**:
there exist absolute constants `α > 0`, `c > 0`, `C > 0` such that for EVERY `Q ≥ 2`, there exists
`q₁ : ℕ` (`q₁ = 0 ∨ 2 ≤ q₁ ≤ Q`) such that for EVERY `q ≤ Q` (`[NeZero q]`) with
`q₁ = 0 ∨ ¬ q₁ ∣ q`, EVERY `χ : DirichletCharacter ℂ q` (`χ ≠ 1`), and EVERY `y ≥ 2` with
`Q ≤ Real.exp (α * Real.sqrt (Real.log y))`:
`‖Stage4ExplicitFormula.psi1Char χ y‖ ≤ C * y ^ 2 * Real.exp (-c * Real.sqrt (Real.log y))`. -/
theorem uniform_psi1Char_bound_of_Q :
    ∃ α : ℝ, 0 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ y : ℝ, 2 ≤ y → Q ≤ Real.exp (α * Real.sqrt (Real.log y)) →
                ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤
                  C * y ^ 2 * Real.exp (-c * Real.sqrt (Real.log y)) := by
  obtain ⟨c₁, hc₁_pos, C₁, hC₁_pos, hbd_all⟩ := uniform_negLogDerivL_nonexceptional_bound
  set c_star : ℝ := min c₁ (1 / 4) with hc_star_def
  have hc_star_pos : 0 < c_star := lt_min hc₁_pos (by norm_num)
  have hc_star_le_c₁ : c_star ≤ c₁ := min_le_left _ _
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  set α : ℝ := Real.sqrt (c_star / 6) with hα_def
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have h6α2 : 6 * α ^ 2 = c_star := by
    rw [hα_def, Real.sq_sqrt (by positivity)]; ring
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  set y₀ : ℝ := max 2 (Real.exp ((2 / α) ^ 2)) with hy₀_def
  have hy₀_ge2 : 2 ≤ y₀ := le_max_left _ _
  set K_large : ℝ :=
    (48 / Real.pi + (27 * C₁ * α ^ 2 / Real.pi) + (18 * C₁ * α ^ 2 / Real.pi)) * (4 / α) ^ 2
  have hK_large_pos : 0 < K_large := by positivity
  set C_small : ℝ := 6 * Real.exp (c_fin * Real.sqrt (Real.log y₀))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨α, hα_pos, c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun Q hQ => ?_⟩
  obtain ⟨q₁, hq₁_spec, hbdQ⟩ := hbd_all Q hQ
  refine ⟨q₁, hq₁_spec, fun q _ hqQ hndvd χ hχ y hy2 hQy => ?_⟩
  by_cases hge : y₀ ≤ y
  · -- Large `y ≥ y₀`: perform the uniform pole-free Perron contour shift!
    have hy0 : 0 < y := by linarith
    set Ly : ℝ := Real.log y with hLy_def
    have hLy_ge_log2 : Real.log 2 ≤ Ly := Real.log_le_log (by norm_num) hy2
    have hLy_pos : 0 < Ly := (Real.log_pos (by norm_num)).trans_le hLy_ge_log2
    set u : ℝ := Real.sqrt Ly with hu_def
    have hu_pos : 0 < u := Real.sqrt_pos.mpr hLy_pos
    have hu_sq : u ^ 2 = Ly := Real.sq_sqrt hLy_pos.le
    have hLy_ge_inv : (2 / α) ^ 2 ≤ Ly := by
      have hexp : Real.exp ((2 / α) ^ 2) ≤ y := (le_max_right _ _).trans hge
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
    -- Contour parameters `c_r = 1 + 1 / (2 Ly)` and `σ_T = 1 - c_star / L_QT`
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
    -- Zero-freeness and uniform log-derivative bound on `[σ_T, c_r] × [-T, T]`
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
      obtain ⟨hnz, hnd⟩ := hbdQ q hqQ hndvd χ hχ z (by linarith) (by linarith)
      refine ⟨hnz, hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 2) hC₁_pos.le)⟩
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
      _ ≤ C_fin * y ^ 2 * Real.exp (-c_fin * u) := by gcongr; exact le_max_left _ _
  · -- Small `2 ≤ y < y₀`: trivial Chebyshev bound `‖psi1Char χ y‖ ≤ 6 * y ^ 2`
    push Not at hge
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
        Real.exp (-c_fin * Real.sqrt (Real.log y₀)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log y)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log y ≤ Real.log y₀ := Real.log_le_log (by linarith) hge.le
      nlinarith [Real.sqrt_le_sqrt hlog]
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log y₀)) = 6 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log y₀) + -c_fin * Real.sqrt (Real.log y₀) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ y‖
        ≤ 6 * y ^ 2 := hpsi1_le
      _ = C_small * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log y₀)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log y)) := by gcongr
      _ ≤ C_fin * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log y)) := by
          gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL UNIFORM-IN-`q` CHARACTER-SUM DECAY (`Q`-PARAMETERIZED)**:
via complex finite-difference de-smoothing (`Stage7PNTInAP.norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le`)
applied at BOTH `y` and `y + h` with the SAME `Q` and the SAME exceptional modulus `q₁`! -/
theorem uniform_chebyshevPsiChar_bound_of_Q :
    ∃ α : ℝ, 0 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ y : ℝ, 2 ≤ y → Q ≤ Real.exp (α * Real.sqrt (Real.log y)) →
                ‖Stage2DirichletAP.chebyshevPsiChar χ y‖ ≤
                  C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
  obtain ⟨α, hα, c₁, hc₁, C₁, hC₁, hpsi1_all⟩ := uniform_psi1Char_bound_of_Q
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (c₁ / 2) c_ψ with hc_fin_def
  have hc_fin_pos : 0 < c_fin := lt_min (by positivity) hc_ψ
  have hc_fin_le1 : c_fin ≤ c₁ / 2 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨α, hα, c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun Q hQ => ?_⟩
  obtain ⟨q₁, hq₁_spec, hpsi1⟩ := hpsi1_all Q hQ
  refine ⟨q₁, hq₁_spec, fun q _ hqQ hndvd χ hχ y hy2 hQy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hLy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  set u : ℝ := Real.sqrt (Real.log y) with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hLy_pos
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := y * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_y : h ≤ y := by nlinarith
  have hyph_ge2 : 2 ≤ y + h := by linarith
  have hyph_le2y : y + h ≤ 2 * y := by linarith
  have hlog_le : Real.log y ≤ Real.log (y + h) := Real.log_le_log hy0 (by linarith)
  have hsqrt_le : u ≤ Real.sqrt (Real.log (y + h)) := Real.sqrt_le_sqrt hlog_le
  have hQ_yh : Q ≤ Real.exp (α * Real.sqrt (Real.log (y + h))) :=
    hQy.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt_le hα.le))
  have hexp_E2 : Real.exp (-c₁ * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; push_cast; nlinarith
  have hexp_yh : Real.exp (-c₁ * Real.sqrt (Real.log (y + h))) ≤ E ^ 2 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hexp_E2
  have hexp_psi : Real.exp (-c_ψ * u) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp_psi_yh : Real.exp (-c_ψ * Real.sqrt (Real.log (y + h))) ≤ E :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hexp_psi
  have hdiff := Stage7PNTInAP.norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hy0.le hh_pos.le
  have hnorm_mul : h * ‖Stage2DirichletAP.chebyshevPsiChar χ y‖ ≤
      ‖Stage4ExplicitFormula.psi1Char χ (y + h)‖ + ‖Stage4ExplicitFormula.psi1Char χ y‖ +
        h * (RHDirect.chebyshevPsi (y + h) - RHDirect.chebyshevPsi y) := by
    have h1 : ‖(h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ y‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ (y + h) - Stage4ExplicitFormula.psi1Char χ y‖ +
        ‖Stage4ExplicitFormula.psi1Char χ (y + h) - Stage4ExplicitFormula.psi1Char χ y -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ y‖ := by
      have htri := norm_sub_le
        (Stage4ExplicitFormula.psi1Char χ (y + h) - Stage4ExplicitFormula.psi1Char χ y)
        (Stage4ExplicitFormula.psi1Char χ (y + h) - Stage4ExplicitFormula.psi1Char χ y -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ y)
      simpa [sub_sub_cancel] using htri
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh_pos.le] at h1
    linarith [norm_sub_le (Stage4ExplicitFormula.psi1Char χ (y + h)) (Stage4ExplicitFormula.psi1Char χ y)]
  have hbd_yh : ‖Stage4ExplicitFormula.psi1Char χ (y + h)‖ ≤ 4 * C₁ * y ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ (y + h)‖
        ≤ C₁ * (y + h) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log (y + h))) :=
          hpsi1 q hqQ hndvd χ hχ (y + h) hyph_ge2 hQ_yh
      _ ≤ C₁ * (2 * y) ^ 2 * E ^ 2 := by
          have hsq : (y + h) ^ 2 ≤ (2 * y) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * y ^ 2 * E ^ 2 := by ring
  have hbd_y : ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤ C₁ * y ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ y‖
        ≤ C₁ * y ^ 2 * Real.exp (-c₁ * u) := hpsi1 q hqQ hndvd χ hχ y hy2 hQy
      _ ≤ C₁ * y ^ 2 * E ^ 2 := by gcongr
  have hpsi_diff_le :
      RHDirect.chebyshevPsi (y + h) - RHDirect.chebyshevPsi y ≤ (1 + 3 * C_ψ) * y * E := by
    have h1 := (abs_le.mp (hpsi (y + h) hyph_ge2)).2
    have h2 := (abs_le.mp (hpsi y hy2)).1
    have h3 : C_ψ * (y + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (y + h))) ≤ 2 * C_ψ * y * E := by
      calc C_ψ * (y + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (y + h)))
          ≤ C_ψ * (2 * y) * E := by gcongr
        _ = 2 * C_ψ * y * E := by ring
    have h4 : C_ψ * y * Real.exp (-c_ψ * u) ≤ C_ψ * y * E := by gcongr
    dsimp only [h] at h1 h2 h3 ⊢
    linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ y‖ ≤ h * (C_fin * y * E) := by
    have hrhs1 : 5 * C₁ * y ^ 2 * E ^ 2 = h * (5 * C₁ * y * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * y * E) + h * ((1 + 3 * C_ψ) * y * E) = h * (C_fin * y * E) := by
      dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

/-- **UNCONDITIONAL UNIFORM PAGE PNT IN ARITHMETIC PROGRESSIONS (`Q`-PARAMETERIZED, `√(log y)`)**:
there exist absolute constants `c > 0`, `C > 0` such that for EVERY `Q ≥ 2`, there exists `q₁ : ℕ`
(`q₁ = 0 ∨ 2 ≤ q₁ ≤ Q`) such that for EVERY `q ≤ Q` (`[NeZero q]`) with `q₁ = 0 ∨ ¬ q₁ ∣ q`,
EVERY `a` with `Nat.Coprime a q`, and EVERY `y ≥ 4` with `Q ≤ Real.exp (c * Real.sqrt (Real.log y))`:
`|chebyshevPsiAP q a y - y / φ(q)| ≤ C * y * Real.exp (-c * Real.sqrt (Real.log y))`. -/
theorem uniform_pnt_psiAP_of_Q :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              ∀ y : ℝ, 4 ≤ y → Q ≤ Real.exp (c * Real.sqrt (Real.log y)) →
                |Stage2DirichletAP.chebyshevPsiAP q a y - y / (q.totient : ℝ)| ≤
                  C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
  obtain ⟨α, hα, c_ch, hc_ch, C_ch, hC_ch, hchar_all⟩ := uniform_chebyshevPsiChar_bound_of_Q
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c : ℝ := min (min α c_ch) (min c_ψ (1 / 2)) with hc_def
  have hc_pos : 0 < c := by positivity
  have hc_le_α : c ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hc_le_ch : c ≤ c_ch := (min_le_left _ _).trans (min_le_right _ _)
  have hc_le_ψ : c ≤ c_ψ := (min_le_right _ _).trans (min_le_left _ _)
  have hc_le_half : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set C : ℝ := C_ψ + 32 * c + C_ch with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨c, hc_pos, C, hC_pos, fun Q hQ => ?_⟩
  obtain ⟨q₁, hq₁_spec, hchar⟩ := hchar_all Q hQ
  refine ⟨q₁, hq₁_spec, fun q _ hqQ hndvd a hcop y hy4 hQy => ?_⟩
  have hy2 : 2 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hLy_gt1 : 1 < Real.log y := by
    have : Real.exp 1 < y := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLy_pos : 0 < Real.log y := zero_lt_one.trans hLy_gt1
  set u : ℝ := Real.sqrt (Real.log y) with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hLy_pos
  have hu_le_Ly : u ≤ Real.log y := by
    have hsq : u ^ 2 = Real.log y := Real.sq_sqrt hLy_pos.le
    nlinarith
  have hQy_α : Q ≤ Real.exp (α * u) :=
    hQy.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc_le_α hu_pos.le))
  have hE1 : |RHDirect.chebyshevPsi y - y| ≤ C_ψ * y * Real.exp (-c * u) := by
    calc |RHDirect.chebyshevPsi y - y|
        ≤ C_ψ * y * Real.exp (-c_ψ * u) := hpsi y hy2
      _ ≤ C_ψ * y * Real.exp (-c * u) := by gcongr
  have hE2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ y‖ ≤ C_ch * y * Real.exp (-c * u) := by
    intro χ hχ
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ y‖
        ≤ C_ch * y * Real.exp (-c_ch * u) := hchar q hqQ hndvd χ hχ y hy2 hQy_α
      _ ≤ C_ch * y * Real.exp (-c * u) := by gcongr
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop hy1
    (by positivity : 0 ≤ C_ch * y * Real.exp (-c * u)) hE1 hE2
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hω_le : (q.primeFactors.card : ℝ) * Real.log y ≤ 32 * c * y * Real.exp (-c * u) := by
    have h1 := Stage2DirichletAP.card_primeFactors_le_log_div_log_two (NeZero.pos q)
    have hlogq_le : Real.log (q : ℝ) ≤ c * u := by
      have hq_exp : (q : ℝ) ≤ Real.exp (c * u) := hqQ.trans hQy
      exact (Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) hq_exp).trans (Real.log_exp _).le
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hcard_le : (q.primeFactors.card : ℝ) ≤ 2 * c * Real.log y := by
      calc (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := h1
        _ ≤ (c * u) / (1 / 2) :=
            div_le_div₀ (by positivity) hlogq_le (by norm_num) hlog2_gt.le
        _ = 2 * c * u := by ring
        _ ≤ 2 * c * Real.log y := mul_le_mul_of_nonneg_left hu_le_Ly (by positivity)
    have hLy2_le : (Real.log y) ^ 2 ≤ 16 * y * Real.exp (-c * u) := by
      have hcu_le : c * u ≤ (1 / 2) * Real.log y := by nlinarith
      have hexp1 : Real.exp (-(1 / 2) * Real.log y) ≤ Real.exp (-c * u) :=
        Real.exp_le_exp.mpr (by linarith)
      have hy_exp : y * Real.exp (-(1 / 2) * Real.log y) = Real.exp ((1 / 2) * Real.log y) := by
        conv_lhs => lhs; rw [← Real.exp_log hy0]
        rw [← Real.exp_add]; congr 1; ring
      have hsq_exp : (Real.log y) ^ 2 * Real.exp (-(1 / 2) * Real.log y) ≤ 16 := by
        have h := sq_mul_exp_neg_two_le_one (u := Real.log y / 4) (by positivity)
        have hEq : (Real.log y) ^ 2 * Real.exp (-(1 / 2) * Real.log y) =
            16 * ((Real.log y / 4) ^ 2 * Real.exp (-2 * (Real.log y / 4))) := by
          rw [show -(1 / 2 : ℝ) * Real.log y = -2 * (Real.log y / 4) by ring]; ring
        rw [hEq]; linarith
      have hLy2_half : (Real.log y) ^ 2 ≤ 16 * Real.exp ((1 / 2) * Real.log y) := by
        have hmul := mul_le_mul_of_nonneg_right hsq_exp (Real.exp_pos ((1 / 2) * Real.log y)).le
        have hcancel : Real.exp (-(1 / 2) * Real.log y) * Real.exp ((1 / 2) * Real.log y) = 1 := by
          rw [← Real.exp_add]; simp
        rw [mul_assoc, hcancel, mul_one] at hmul
        exact hmul
      calc (Real.log y) ^ 2 ≤ 16 * Real.exp ((1 / 2) * Real.log y) := hLy2_half
        _ = 16 * (y * Real.exp (-(1 / 2) * Real.log y)) := by rw [hy_exp]
        _ ≤ 16 * (y * Real.exp (-c * u)) := by gcongr
        _ = 16 * y * Real.exp (-c * u) := by ring
    calc (q.primeFactors.card : ℝ) * Real.log y
        ≤ (2 * c * Real.log y) * Real.log y := mul_le_mul_of_nonneg_right hcard_le hLy_pos.le
      _ = 2 * c * (Real.log y) ^ 2 := by ring
      _ ≤ 2 * c * (16 * y * Real.exp (-c * u)) := mul_le_mul_of_nonneg_left hLy2_le (by positivity)
      _ = 32 * c * y * Real.exp (-c * u) := by ring
  have hdiv_le :
      (C_ψ * y * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log y) / (q.totient : ℝ) ≤
        (C_ψ + 32 * c) * y * Real.exp (-c * u) := by
    calc (C_ψ * y * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log y) / (q.totient : ℝ)
        ≤ (C_ψ * y * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log y) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hphi_ge1
      _ = C_ψ * y * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log y := div_one _
      _ ≤ (C_ψ + 32 * c) * y * Real.exp (-c * u) := by linarith
  calc |Stage2DirichletAP.chebyshevPsiAP q a y - y / (q.totient : ℝ)|
      ≤ (C_ψ * y * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log y) / (q.totient : ℝ) +
          C_ch * y * Real.exp (-c * u) := htri
    _ ≤ (C_ψ + 32 * c) * y * Real.exp (-c * u) + C_ch * y * Real.exp (-c * u) := by linarith
    _ = C * y * Real.exp (-c * u) := by dsimp only [C]; ring

/-- **UNCONDITIONAL PAGE'S UNIFORM PNT IN ARITHMETIC PROGRESSIONS (`√(log x)` SHARP FORM,
`0` ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 4, ∃ q₁ : ℕ, ∀ q [NeZero q], q ≤ exp (c √(log x)) →
  (q₁ = 0 ∨ ¬ q₁ ∣ q) → ∀ a, Nat.Coprime a q →
  |ψ(x; q, a) - x / φ(q)| ≤ C * x * exp (-c √(log x))`. -/
theorem page_uniform_pnt_psiAP_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x →
        ∃ q₁ : ℕ,
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
            (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
                C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C₀, hC₀, hQ_all⟩ := uniform_pnt_psiAP_of_Q
  -- Cover `Real.exp (c * √(log x)) < 2` by the trivial bound `|ψ(x; q, a) - x/φ(q)| ≤ 7 * x`
  set C_fin : ℝ := max C₀ 14
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨c, hc, C_fin, hC_fin_pos, fun x hx4 => ?_⟩
  by_cases hQ2 : 2 ≤ Real.exp (c * Real.sqrt (Real.log x))
  · obtain ⟨q₁, _, hbd⟩ := hQ_all (Real.exp (c * Real.sqrt (Real.log x))) hQ2
    refine ⟨q₁, fun q _ hq hndvd a hcop => ?_⟩
    exact (hbd q hq hndvd a hcop x hx4 le_rfl).trans (by gcongr; exact le_max_left _ _)
  · push Not at hQ2
    refine ⟨0, fun q _ _ _ a _ => ?_⟩
    have hpsi_le : Stage2DirichletAP.chebyshevPsiAP q a x ≤ 6 * x := by
      have h1 : Stage2DirichletAP.chebyshevPsiAP q a x ≤ RHDirect.chebyshevPsi x := by
        unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
        refine Finset.sum_le_sum fun n _ => ?_
        split_ifs
        · exact le_rfl
        · exact ArithmeticFunction.vonMangoldt_nonneg
      exact h1.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
    have hpsi_nn : 0 ≤ Stage2DirichletAP.chebyshevPsiAP q a x :=
      Stage2DirichletAP.chebyshevPsiAP_nonneg q a x
    have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    have hmain_le : x / (q.totient : ℝ) ≤ x := by
      calc x / (q.totient : ℝ) ≤ x / 1 := div_le_div_of_nonneg_left (by linarith) zero_lt_one hphi_ge1
        _ = x := div_one x
    have habs_le : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ 7 * x := by
      rw [abs_le]
      have hmain_nn : 0 ≤ x / (q.totient : ℝ) := div_nonneg (by linarith) (by linarith)
      constructor <;> linarith
    have hexp_ge : (1 / 2 : ℝ) ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hinv : (2 : ℝ)⁻¹ ≤ (Real.exp (c * Real.sqrt (Real.log x)))⁻¹ :=
        inv_anti₀ (Real.exp_pos _) hQ2.le
      rw [← Real.exp_neg] at hinv
      simpa [neg_mul] using hinv
    calc |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)|
        ≤ 7 * x := habs_le
      _ ≤ 14 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by nlinarith
      _ ≤ C_fin * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL PAGE'S UNIFORM PNT IN ARITHMETIC PROGRESSIONS (`(log x)^(1/20)` FORM,
`0` ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 4, ∃ q₁ : ℕ, ∀ q [NeZero q],
  q ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ)) → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
  ∀ a, Nat.Coprime a q →
  |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem page_uniform_pnt_psiAP :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x →
        ∃ q₁ : ℕ,
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ)) →
            (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
                C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hsqrt⟩ := page_uniform_pnt_psiAP_sqrt
  refine ⟨c, hc, C, hC, fun x hx4 => ?_⟩
  obtain ⟨q₁, hbd⟩ := hsqrt x hx4
  have hLx_gt1 : 1 ≤ Real.log x := by
    have : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) this)
  have hrpow_le : (Real.log x) ^ (1 / 20 : ℝ) ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hLx_gt1 (by norm_num)
  refine ⟨q₁, fun q _ hq hndvd a hcop => ?_⟩
  have hq_sqrt : (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) :=
    hq.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow_le hc.le))
  have hexp_le : Real.exp (-c * Real.sqrt (Real.log x)) ≤
      Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact (hbd q hq_sqrt hndvd a hcop).trans (by gcongr)

/-! ## Section 3: Non-Exceptional Dyadic Prime Existence & Titchmarsh Divisor Upper Bound -/

/-- **UNCONDITIONAL EFFECTIVE DYADIC PRIME EXISTENCE FOR NON-EXCEPTIONAL MODULI (`0` ASSUMPTIONS!)**:
there exist `c > 0` and `x₀ ≥ 8` such that for every `x ≥ x₀`, there exists at most ONE
exceptional modulus `q₁ : ℕ` such that for EVERY `q ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ))`
(`[NeZero q]`) with `q₁ = 0 ∨ ¬ q₁ ∣ q` and EVERY `a` with `Nat.Coprime a q`, there exists a prime
`p ∈ (x / 2, x]` with `p ≡ a [MOD q]`. -/
theorem exists_prime_in_dyadic_ap_uniform_nonexceptional :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 8 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∃ q₁ : ℕ,
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ)) →
            (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x / 2 < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  obtain ⟨c_ap, hc_ap, C_ap, hC_ap, hQ_all⟩ := uniform_pnt_psiAP_of_Q
  set c_L : ℝ := min (c_ap / 4) (1 / 8) with hcL_def
  have hcL_pos : 0 < c_L := lt_min (by positivity) (by norm_num)
  have hcL_le_qtr : c_L ≤ c_ap / 4 := min_le_left _ _
  have hcL_le_8 : c_L ≤ 1 / 8 := min_le_right _ _
  -- Threshold `L₀` large enough that `exp(c_L * L₀^(1/20)) ≥ 2`, `exp(c_L * L₀^(1/20)) > 6 * C_ap + 1`,
  -- and `16 * log x / √x < exp(-c_L * (log x)^(1/20))`
  set M_req : ℝ := max 2 (max (12 * C_ap + 4) 64)
  have hM_req_ge2 : 2 ≤ M_req := le_max_left _ _
  set L₀ : ℝ := max 16 ((Real.log M_req / c_L) ^ (20 : ℕ))
  have hL₀_ge16 : 16 ≤ L₀ := le_max_left _ _
  set x₀ : ℝ := max 8 (Real.exp L₀)
  have hx₀_ge8 : 8 ≤ x₀ := le_max_left _ _
  refine ⟨c_L, hcL_pos, x₀, hx₀_ge8, fun x hx => ?_⟩
  have hx8 : 8 ≤ x := hx₀_ge8.trans hx
  have hx0 : 0 < x := by linarith
  have hLx_ge : L₀ ≤ Real.log x :=
    (Real.log_exp L₀).symm.trans_le (Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx))
  have hLx_ge16 : 16 ≤ Real.log x := hL₀_ge16.trans hLx_ge
  have hLx_pos : 0 < Real.log x := by linarith
  set w : ℝ := (Real.log x) ^ (1 / 20 : ℝ) with hw_def
  have hw_pos : 0 < w := Real.rpow_pos_of_pos hLx_pos _
  have hw_pow20 : w ^ (20 : ℕ) = Real.log x := by
    dsimp only [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLx_pos.le]; norm_num
  have hM_le_exp : M_req ≤ Real.exp (c_L * w) := by
    have hlogM_pos : 0 < Real.log M_req := Real.log_pos (by linarith)
    have hpow : (Real.log M_req / c_L) ^ (20 : ℕ) ≤ w ^ (20 : ℕ) := by
      rw [hw_pow20]; exact (le_max_right _ _).trans hLx_ge
    have hbase : Real.log M_req / c_L ≤ w := by
      by_contra hlt; push Not at hlt
      have := pow_lt_pow_left₀ hlt hw_pos.le (by norm_num : 20 ≠ 0)
      linarith
    have hmul : Real.log M_req ≤ c_L * w := by
      have := mul_le_mul_of_nonneg_left hbase hcL_pos.le
      rwa [mul_div_cancel₀ _ hcL_pos.ne'] at this
    calc M_req = Real.exp (Real.log M_req) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (c_L * w) := Real.exp_le_exp.mpr hmul
  set Q : ℝ := Real.exp (c_L * w)
  have hQ_ge2 : 2 ≤ Q := hM_req_ge2.trans hM_le_exp
  -- Apply `uniform_pnt_psiAP_of_Q` at `Q` to obtain ONE `q₁` working at BOTH `x` and `x / 2`!
  obtain ⟨q₁, _, hbdQ⟩ := hQ_all Q hQ_ge2
  refine ⟨q₁, fun q _ hqQ hndvd a hcop => ?_⟩
  -- Check `log (x / 2) ≥ (1 / 2) * log x` and `w ≤ (1 / 2) * √(log (x / 2))`
  have hlog_half : (1 / 2) * Real.log x ≤ Real.log (x / 2) := by
    rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hw_le_sqrt : w ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hw_le_sqrt_half : w ≤ Real.sqrt (Real.log (x / 2)) := by
    have h1 : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log (x / 2)) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow, Real.sq_sqrt hLx_pos.le]
      linarith
    have h2 : w ≤ (Real.log x) ^ (1 / 2 : ℝ) / 2 := by
      have hsplit : (Real.log x) ^ (1 / 2 : ℝ) = w * (Real.log x) ^ (9 / 20 : ℝ) := by
        dsimp only [w]
        rw [← Real.rpow_add hLx_pos]; norm_num
      have hge2 : 2 ≤ (Real.log x) ^ (9 / 20 : ℝ) := by
        have h16 : (16 : ℝ) ^ (9 / 20 : ℝ) ≤ (Real.log x) ^ (9 / 20 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hLx_ge16 (by norm_num)
        have h2_le : (2 : ℝ) ≤ (16 : ℝ) ^ (9 / 20 : ℝ) := by
          have hpow : (2 : ℝ) ^ (20 : ℕ) ≤ ((16 : ℝ) ^ (9 / 20 : ℝ)) ^ (20 : ℕ) := by
            conv_rhs => rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
            norm_num
          by_contra hlt; push Not at hlt
          have := pow_lt_pow_left₀ hlt (Real.rpow_nonneg (by norm_num) _) (by norm_num : 20 ≠ 0)
          linarith
        exact h2_le.trans h16
      rw [hsplit]
      nlinarith
    rw [Real.sqrt_eq_rpow] at h1
    linarith
  have hQ_x : Q ≤ Real.exp (c_ap * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hQ_half : Q ≤ Real.exp (c_ap * Real.sqrt (Real.log (x / 2))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpsi_x := hbdQ q hqQ hndvd a hcop x (by linarith) hQ_x
  have hpsi_half := hbdQ q hqQ hndvd a hcop (x / 2) (by linarith) hQ_half
  -- Lower bound `ψ(x; q, a) - ψ(x / 2; q, a)`
  have hdiff_ge :
      x / (2 * (q.totient : ℝ)) -
          C_ap * x * Real.exp (-c_ap * Real.sqrt (Real.log x)) -
          C_ap * (x / 2) * Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤
        Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevPsiAP q a (x / 2) := by
    have h1 := (abs_le.mp hpsi_x).1
    have h2 := (abs_le.mp hpsi_half).2
    have hmain : x / (q.totient : ℝ) - (x / 2) / (q.totient : ℝ) = x / (2 * (q.totient : ℝ)) := by ring
    linarith
  have hphi_le_Q : (q.totient : ℝ) ≤ Q :=
    (by exact_mod_cast Nat.totient_le q : (q.totient : ℝ) ≤ (q : ℝ)).trans hqQ
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hmain_ge : x / (2 * Q) ≤ x / (2 * (q.totient : ℝ)) :=
    div_le_div_of_nonneg_left hx0.le (by positivity) (by linarith)
  -- Error 1 + Error 2 ≤ (3/2) C_ap * x / Q ^ 2 ≤ x / (8 * Q)
  have hexp_le_Q2 : Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤ 1 / Q ^ 2 := by
    have h1 : 2 * (c_L * w) ≤ c_ap * Real.sqrt (Real.log (x / 2)) := by nlinarith
    have h2 : Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤ Real.exp (-(2 * (c_L * w))) :=
      Real.exp_le_exp.mpr (by linarith)
    refine h2.trans_eq ?_
    rw [Real.exp_neg, show 2 * (c_L * w) = ((2 : ℕ) : ℝ) * (c_L * w) by norm_num,
      Real.exp_nat_mul, one_div]
  have hexp_x_le : Real.exp (-c_ap * Real.sqrt (Real.log x)) ≤ 1 / Q ^ 2 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (by linarith : x / 2 ≤ x))])).trans hexp_le_Q2
  have herr_ap :
      C_ap * x * Real.exp (-c_ap * Real.sqrt (Real.log x)) +
        C_ap * (x / 2) * Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤ x / (8 * Q) := by
    have hQ_ge : 12 * C_ap ≤ Q := by
      have : 12 * C_ap + 4 ≤ M_req := (le_max_left _ _).trans (le_max_right _ _)
      linarith
    have h1 : C_ap * x * Real.exp (-c_ap * Real.sqrt (Real.log x)) +
        C_ap * (x / 2) * Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤
        (3 / 2) * C_ap * x / Q ^ 2 := by
      have ha : C_ap * x * Real.exp (-c_ap * Real.sqrt (Real.log x)) ≤ C_ap * x * (1 / Q ^ 2) := by gcongr
      have hb : C_ap * (x / 2) * Real.exp (-c_ap * Real.sqrt (Real.log (x / 2))) ≤ C_ap * (x / 2) * (1 / Q ^ 2) := by gcongr
      linarith [show C_ap * x * (1 / Q ^ 2) + C_ap * (x / 2) * (1 / Q ^ 2) = (3 / 2) * C_ap * x / Q ^ 2 by ring]
    have h2 : (3 / 2) * C_ap * x / Q ^ 2 ≤ x / (8 * Q) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Q)) (by positivity)]
      have hmul : 12 * C_ap * Q ≤ Q ^ 2 := by nlinarith
      have hmul2 := mul_le_mul_of_nonneg_left hmul hx0.le
      linarith
    exact h1.trans h2
  -- Prime-power error `√x * log x < x / (4 * Q)`
  have herr_pp : Real.sqrt x * Real.log x < x / (4 * Q) := by
    -- `Q = exp(c_L * w) ≤ exp((1/8) * log x) = x^(1/8)`, and `4 * log x * x^(1/8) < x^(1/2)`!
    have hQ_le_x8 : Q ≤ Real.exp ((1 / 8) * Real.log x) := by
      apply Real.exp_le_exp.mpr
      have hw_le_Lx : w ≤ Real.log x := hw_le_sqrt.trans (by
        have hsq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x := Real.sq_sqrt hLx_pos.le
        nlinarith [Real.sqrt_nonneg (Real.log x)])
      nlinarith
    have hlog_le_x4 : 4 * Real.log x ≤ 16 * Real.exp ((1 / 4) * Real.log x) := by
      have h := Real.add_one_le_exp ((1 / 4) * Real.log x)
      linarith
    have hprod : 4 * Q * (Real.sqrt x * Real.log x) < x := by
      have hsqrt_exp : Real.sqrt x = Real.exp ((1 / 2) * Real.log x) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; congr 1; ring
      have h1 : 4 * Q * (Real.sqrt x * Real.log x) ≤
          16 * Real.exp ((7 / 8) * Real.log x) := by
        calc 4 * Q * (Real.sqrt x * Real.log x)
            = Q * Real.sqrt x * (4 * Real.log x) := by ring
          _ ≤ Real.exp ((1 / 8) * Real.log x) * Real.exp ((1 / 2) * Real.log x) *
                (16 * Real.exp ((1 / 4) * Real.log x)) := by
              rw [← hsqrt_exp]
              gcongr
          _ = 16 * Real.exp ((7 / 8) * Real.log x) := by
              rw [show Real.exp ((1 / 8) * Real.log x) * Real.exp ((1 / 2) * Real.log x) *
                  (16 * Real.exp ((1 / 4) * Real.log x)) =
                  16 * (Real.exp ((1 / 8) * Real.log x) * Real.exp ((1 / 2) * Real.log x) *
                  Real.exp ((1 / 4) * Real.log x)) by ring,
                ← Real.exp_add, ← Real.exp_add]
              congr 2; ring
      have h2 : 16 < Real.exp ((1 / 8) * Real.log x) := by
        have h64 : 64 ≤ Q := ((le_max_right _ _).trans (le_max_right _ _)).trans hM_le_exp
        linarith
      have h3 : 16 * Real.exp ((7 / 8) * Real.log x) < x := by
        have hx_eq : x = Real.exp ((1 / 8) * Real.log x) * Real.exp ((7 / 8) * Real.log x) := by
          rw [← Real.exp_add, show (1 / 8) * Real.log x + (7 / 8) * Real.log x = Real.log x by ring,
            Real.exp_log hx0]
        conv_rhs => rw [hx_eq]
        exact mul_lt_mul_of_pos_right h2 (Real.exp_pos _)
      exact lt_of_le_of_lt h1 h3
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Q)]
    linarith
  have hgt : Real.sqrt x * Real.log x <
      Stage2DirichletAP.chebyshevPsiAP q a x - Stage2DirichletAP.chebyshevPsiAP q a (x / 2) := by
    have h4 : x / (4 * Q) + x / (8 * Q) < x / (2 * Q) := by
      have : 0 < x / (8 * Q) := by positivity
      linarith [show x / (2 * Q) = x / (4 * Q) + x / (8 * Q) + x / (8 * Q) by ring]
    linarith
  exact Stage2DirichletAP.exists_prime_in_Ioc_of_psiAP_diff_gt q a (by linarith) (by linarith) hgt

/-! ## Section 4: Unconditional Titchmarsh Shifted-Prime Divisor Upper Bound (`0` Assumptions!) -/

/-- Elementary telescoping sum bound: `∑_{j=2}^M 1 / (j * (j - 1)) ≤ 1` for all `M : ℕ`. -/
private lemma sum_inv_mul_sub_one_le_one (M : ℕ) :
    ∑ j ∈ Finset.Icc 2 M, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) ≤ 1 := by
  by_cases hM : M = 0
  · subst hM; simp
  · suffices htel : ∀ k : ℕ, 1 ≤ k →
        ∑ j ∈ Finset.Icc 2 k, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) = 1 - 1 / (k : ℝ) by
      rw [htel M (by omega)]
      have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
      linarith
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ihk =>
      have hIcc' : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc', Finset.sum_insert (by simp), ihk]
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      push_cast
      field_simp [hk_pos.ne', hk1_pos.ne']
      ring

/-- **Unconditional Upper Bound on the Squarefree Reciprocal `k * φ(k)` Sum**:
for every `M : ℕ`,
`∑_{1 ≤ k ≤ M, Squarefree k} 1 / (k * φ(k)) ≤ 3`. -/
theorem sum_squarefree_inv_mul_totient_le_three (M : ℕ) :
    ∑ k ∈ (Finset.Icc 1 M).filter Squarefree, (1 : ℝ) / ((k : ℝ) * (k.totient : ℝ)) ≤ 3 := by
  set P : Finset ℕ := (Finset.Icc 2 M).filter Nat.Prime
  have hmaps : ∀ k ∈ (Finset.Icc 1 M).filter Squarefree, k.primeFactors ∈ P.powerset := by
    intro k hk
    obtain ⟨hkI, hksqf⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hkI
    refine Finset.mem_powerset.mpr fun p hp => ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ k := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.two_le, (Nat.le_of_dvd (by omega) hpdvd).trans hkM⟩, hpr⟩
  have hinj : Set.InjOn Nat.primeFactors (((Finset.Icc 1 M).filter Squarefree : Finset ℕ) : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hs1 : Squarefree k₁ := (Finset.mem_filter.mp hk₁).2
    have hs2 : Squarefree k₂ := (Finset.mem_filter.mp hk₂).2
    rw [← Nat.prod_primeFactors_of_squarefree hs1, ← Nat.prod_primeFactors_of_squarefree hs2, heq]
  have hval : ∀ k ∈ (Finset.Icc 1 M).filter Squarefree,
      (1 : ℝ) / ((k : ℝ) * (k.totient : ℝ)) =
        ∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro k hk
    have hsqf : Squarefree k := (Finset.mem_filter.mp hk).2
    have hk_prod : k = ∏ p ∈ k.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsqf).symm
    have hphi_prod : k.totient = ∏ p ∈ k.primeFactors, (p - 1) :=
      Stage7SieveMethods.totient_eq_prod_sub_one_of_squarefree hsqf
    have hmul : (k : ℝ) * (k.totient : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1)) := by
      calc (k : ℝ) * (k.totient : ℝ)
          = ((∏ p ∈ k.primeFactors, p : ℕ) : ℝ) * ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℝ) := by
            rw [← hk_prod, ← hphi_prod]
        _ = (∏ p ∈ k.primeFactors, (p : ℝ)) * (∏ p ∈ k.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
            rw [Nat.cast_prod, Nat.cast_prod]
        _ = ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := Finset.prod_mul_distrib.symm
        _ = ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1)) := by
            refine Finset.prod_congr rfl fun p hp => ?_
            rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
    rw [hmul, one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun _ _ => (one_div _).symm
  have hterm_nn : ∀ S ∈ P.powerset,
      0 ≤ ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro S hS
    refine Finset.prod_nonneg fun p hp => ?_
    have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp hS hp)).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    exact div_nonneg zero_le_one (by nlinarith)
  have hprod_le_exp :
      ∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        Real.exp (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
      have : 0 ≤ (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := div_nonneg zero_le_one (by nlinarith)
      linarith
    · simpa [add_comm] using Real.add_one_le_exp ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
  have hsum_P_le : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ j ∈ Finset.Icc 2 M, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j hj _ => ?_
          have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
          exact div_nonneg zero_le_one (by nlinarith)
      _ ≤ 1 := sum_inv_mul_sub_one_le_one M
  calc ∑ k ∈ (Finset.Icc 1 M).filter Squarefree, (1 : ℝ) / ((k : ℝ) * (k.totient : ℝ))
      = ∑ k ∈ (Finset.Icc 1 M).filter Squarefree,
          ∏ p ∈ k.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
        Finset.sum_congr rfl hval
    _ = ∑ S ∈ ((Finset.Icc 1 M).filter Squarefree).image Nat.primeFactors,
          ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
        (Finset.sum_image (f := fun S : Finset ℕ =>
          ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) hinj).symm
    _ ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          fun S hS _ => hterm_nn S hS
    _ = ∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := hprod_le_exp
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum_P_le
    _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

/-- **UNCONDITIONAL RECIPROCAL TOTIENT SUM UPPER BOUND**:
for EVERY `M ≥ 1`,
`∑_{d=1}^M 1 / φ(d) ≤ 3 * (Real.log M + 1)`. -/
theorem sum_inv_totient_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d.totient : ℝ) ≤ 3 * (Real.log (M : ℝ) + 1) := by
  -- Use `1 / φ(d) = ∑_{k ∣ d, Squarefree k} 1 / (d * φ(k))` from `Stage7SieveMethods.sum_divisors_squarefree_inv_totient`
  have hrewrite : ∀ d ∈ Finset.Icc 1 M,
      (1 : ℝ) / (d.totient : ℝ) =
        ∑ k ∈ d.divisors.filter Squarefree, (1 : ℝ) / ((d : ℝ) * (k.totient : ℝ)) := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
    have hsum := Stage7SieveMethods.sum_divisors_squarefree_inv_totient hd_pos
    have hmul := congrArg ((d : ℝ)⁻¹ * ·) hsum
    rw [Finset.mul_sum] at hmul
    have hlhs : (d : ℝ)⁻¹ * ((d : ℝ) / (d.totient : ℝ)) = 1 / (d.totient : ℝ) := by
      field_simp [hdR.ne']
    rw [hlhs] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl hrewrite]
  -- Swap sums via `(d, k) ↦ (k, d / k)` into `((Icc 1 M).filter Squarefree) ×ˢ (Icc 1 M)`
  set K : Finset ℕ := (Finset.Icc 1 M).filter Squarefree
  have hswap :
      ∑ d ∈ Finset.Icc 1 M, ∑ k ∈ d.divisors.filter Squarefree, (1 : ℝ) / ((d : ℝ) * (k.totient : ℝ)) ≤
        ∑ k ∈ K, ∑ m ∈ Finset.Icc 1 M,
          ((1 : ℝ) / ((k : ℝ) * (k.totient : ℝ))) * ((m : ℝ))⁻¹ := by
    have hpair :
        ∑ d ∈ Finset.Icc 1 M, ∑ k ∈ d.divisors.filter Squarefree, (1 : ℝ) / ((d : ℝ) * (k.totient : ℝ)) =
          ∑ dk ∈ (Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree),
            (1 : ℝ) / ((dk.1 : ℝ) * (dk.2.totient : ℝ)) :=
      (Finset.sum_sigma (Finset.Icc 1 M) (fun d => d.divisors.filter Squarefree)
        (fun dk => (1 : ℝ) / ((dk.1 : ℝ) * (dk.2.totient : ℝ)))).symm
    rw [hpair, ← Finset.sum_product']
    let f : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun dk => (dk.2, dk.1 / dk.2)
    have hmaps : ∀ dk ∈ (Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree),
        f dk ∈ K ×ˢ Finset.Icc 1 M := by
      intro dk hdk
      obtain ⟨hdI, hkF⟩ := Finset.mem_sigma.mp hdk
      obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hdI
      obtain ⟨hk_div, hksqf⟩ := Finset.mem_filter.mp hkF
      obtain ⟨hkd, -⟩ := Nat.mem_divisors.mp hk_div
      have hk_pos : 0 < dk.2 := Nat.pos_of_ne_zero hksqf.ne_zero
      have hk_le : dk.2 ≤ M := (Nat.le_of_dvd (by omega) hkd).trans hdM
      have hm_pos : 0 < dk.1 / dk.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hkd) hk_pos
      have hm_le : dk.1 / dk.2 ≤ M := (Nat.div_le_self dk.1 dk.2).trans hdM
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, hksqf⟩,
        Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩⟩
    have hinj : Set.InjOn f
        (((Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree) : Finset (Σ _ : ℕ, ℕ)) :
          Set (Σ _ : ℕ, ℕ)) := by
      intro a ha b hb heq
      have h2 : a.2 = b.2 := congrArg Prod.fst heq
      have hdiv : a.1 / a.2 = b.1 / b.2 := congrArg Prod.snd heq
      have ha_dvd : a.2 ∣ a.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).2).1).1
      have hb_dvd : b.2 ∣ b.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hb).2).1).1
      have h1 : a.1 = b.1 := by
        rw [← Nat.mul_div_cancel' ha_dvd, ← Nat.mul_div_cancel' hb_dvd, hdiv, h2]
      cases a; cases b; simp only at h1 h2; subst h1; subst h2; rfl
    have hval : ∀ dk ∈ (Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree),
        (1 : ℝ) / ((dk.1 : ℝ) * (dk.2.totient : ℝ)) =
          ((1 : ℝ) / (((f dk).1 : ℝ) * ((f dk).1.totient : ℝ))) * (((f dk).2 : ℝ))⁻¹ := by
      intro dk hdk
      have hdvd : dk.2 ∣ dk.1 := (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hdk).2).1).1
      have hmul : (dk.1 : ℝ) = (dk.2 : ℝ) * ((dk.1 / dk.2 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
      dsimp only [f]
      rw [hmul]; ring
    calc ∑ dk ∈ (Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree),
            (1 : ℝ) / ((dk.1 : ℝ) * (dk.2.totient : ℝ))
        = ∑ dk ∈ (Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree),
            ((1 : ℝ) / (((f dk).1 : ℝ) * ((f dk).1.totient : ℝ))) * (((f dk).2 : ℝ))⁻¹ :=
          Finset.sum_congr rfl hval
      _ = ∑ km ∈ ((Finset.Icc 1 M).sigma (fun d => d.divisors.filter Squarefree)).image f,
            ((1 : ℝ) / ((km.1 : ℝ) * (km.1.totient : ℝ))) * ((km.2 : ℝ))⁻¹ :=
          (Finset.sum_image (f := fun km : ℕ × ℕ =>
            ((1 : ℝ) / ((km.1 : ℝ) * (km.1.totient : ℝ))) * ((km.2 : ℝ))⁻¹) hinj).symm
      _ ≤ ∑ km ∈ K ×ˢ Finset.Icc 1 M,
            ((1 : ℝ) / ((km.1 : ℝ) * (km.1.totient : ℝ))) * ((km.2 : ℝ))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
            fun _ _ _ => by positivity
  have hprod_sum :
      ∑ k ∈ K, ∑ m ∈ Finset.Icc 1 M,
          ((1 : ℝ) / ((k : ℝ) * (k.totient : ℝ))) * ((m : ℝ))⁻¹ =
        (∑ k ∈ K, (1 : ℝ) / ((k : ℝ) * (k.totient : ℝ))) *
          (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have h1 := sum_squarefree_inv_mul_totient_le_three M
  have h2 := Stage5DirichletLZeroFree.harmonic_sum_le_log_add_one hM
  have hharm_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ d ∈ Finset.Icc 1 M, ∑ k ∈ d.divisors.filter Squarefree, (1 : ℝ) / ((d : ℝ) * (k.totient : ℝ))
      ≤ (∑ k ∈ K, (1 : ℝ) / ((k : ℝ) * (k.totient : ℝ))) *
          (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) := hswap.trans_eq hprod_sum
    _ ≤ 3 * (Real.log (M : ℝ) + 1) :=
        mul_le_mul h1 h2 hharm_nn (by norm_num)

/-- **Dirichlet Hyperbola Splitting for the Divisor Function**:
for every `m ≥ 1`, `d(m) ≤ 2 * #{d ∈ m.divisors : d ≤ Nat.sqrt m}`. -/
theorem card_divisors_le_two_mul_le_sqrt {m : ℕ} (hm : 1 ≤ m) :
    m.divisors.card ≤ 2 * (m.divisors.filter (fun d => d ≤ Nat.sqrt m)).card := by
  set D₁ : Finset ℕ := m.divisors.filter (fun d => d ≤ Nat.sqrt m)
  have hsub : m.divisors ⊆ D₁ ∪ D₁.image (fun d => m / d) := by
    intro d hd
    by_cases hle : d ≤ Nat.sqrt m
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, hle⟩)
    · apply Finset.mem_union_right
      obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp hd
      set e : ℕ := m / d
      have hed : d * e = m := Nat.mul_div_cancel' hdm
      have he_dvd : e ∣ m := ⟨d, by rw [mul_comm, hed]⟩
      have he_le : e ≤ Nat.sqrt m := by
        by_contra hgt
        have h1 : Nat.sqrt m + 1 ≤ d := by omega
        have h2 : Nat.sqrt m + 1 ≤ e := by omega
        have hmul : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ d * e := Nat.mul_le_mul h1 h2
        have hlt : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
        omega
      have he_pos : 0 < e := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hed; omega
      have hdiv_eq : m / e = d := by
        rw [← hed, Nat.mul_div_cancel _ he_pos]
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨he_dvd, hm0⟩, he_le⟩, hdiv_eq⟩
  calc m.divisors.card
      ≤ (D₁ ∪ D₁.image (fun d => m / d)).card := Finset.card_le_card hsub
    _ ≤ D₁.card + (D₁.image (fun d => m / d)).card := Finset.card_union_le _ _
    _ ≤ D₁.card + D₁.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * D₁.card := by omega

/-- **UNCONDITIONAL TITCHMARSH SHIFTED-PRIME DIVISOR UPPER BOUND (EXPLICIT CONSTANT `120`,
`0` ASSUMPTIONS!)**:
for EVERY `n : ℕ`:
`∑_{p ∈ (Icc 2 n).filter Nat.Prime} d(p - 1) ≤ 120 * n`. -/
theorem titchmarsh_divisor_upper_bound_explicit (n : ℕ) :
    ((∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card : ℕ) : ℝ) ≤
      120 * (n : ℝ) := by
  by_cases hn : n < 81
  · -- Small `n < 81`: trivial bound `d(p - 1) ≤ p - 1 ≤ 79`
    have hnat : ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card ≤ 120 * n := by
      calc ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card
          ≤ ∑ _p ∈ (Finset.Icc 2 n).filter Nat.Prime, 120 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_mem := (Finset.mem_filter.mp hp).1
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp_mem).1
            have hpn : p ≤ n := (Finset.mem_Icc.mp hp_mem).2
            have hsub : (p - 1).divisors ⊆ Finset.Icc 1 (p - 1) := by
              intro d hd
              obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hd
              exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
                Nat.le_of_dvd (by omega) hdvd⟩
            calc (p - 1).divisors.card ≤ (Finset.Icc 1 (p - 1)).card := Finset.card_le_card hsub
              _ = p - 1 := by rw [Nat.card_Icc]; omega
              _ ≤ 120 := by omega
        _ = ((Finset.Icc 2 n).filter Nat.Prime).card * 120 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ n * 120 := Nat.mul_le_mul_right 120
            ((Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega))
        _ = 120 * n := mul_comm n 120
    exact_mod_cast hnat
  · -- Main regime `n ≥ 81`: Dirichlet hyperbola splitting + `Stage7SieveMethods.brun_titchmarsh_ap`!
    push Not at hn
    set M : ℕ := Nat.sqrt n with hM_def
    have hM_ge9 : 9 ≤ M := Nat.le_sqrt.mpr (by omega)
    have hM_ge1 : 1 ≤ M := by omega
    set P : Finset ℕ := (Finset.Icc 2 n).filter Nat.Prime
    -- Step 1: Hyperbola splitting + order-of-summation swap
    have hhyper :
        ∑ p ∈ P, (Nat.divisors (p - 1)).card ≤
          2 * ∑ d ∈ Finset.Icc 1 M,
            ((Finset.Ioc 0 (0 + n)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD d])).card := by
      have h1 : ∑ p ∈ P, (Nat.divisors (p - 1)).card ≤
          ∑ p ∈ P, 2 * ((Finset.Icc 1 M).filter (fun d => d ∣ p - 1)).card := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpI := (Finset.mem_filter.mp hp).1
        have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hpI).1
        have hpn : p ≤ n := (Finset.mem_Icc.mp hpI).2
        refine (card_divisors_le_two_mul_le_sqrt (by omega : 1 ≤ p - 1)).trans ?_
        refine Nat.mul_le_mul_left 2 (Finset.card_le_card fun d hd => ?_)
        obtain ⟨hd_div, hd_sq⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdp, -⟩ := Nat.mem_divisors.mp hd_div
        have hsq_le : Nat.sqrt (p - 1) ≤ M := Nat.sqrt_le_sqrt (by omega)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.pos_of_dvd_of_pos hdp (by omega), hd_sq.trans hsq_le⟩, hdp⟩
      have hswap :
          ∑ p ∈ P, ((Finset.Icc 1 M).filter (fun d => d ∣ p - 1)).card =
            ∑ d ∈ Finset.Icc 1 M, (P.filter (fun p => d ∣ p - 1)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      rw [← Finset.mul_sum, hswap] at h1
      refine h1.trans (Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun d _ => ?_))
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨hpP, hdp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpI, hpr⟩ := Finset.mem_filter.mp hpP
      obtain ⟨hp2, hpn⟩ := Finset.mem_Icc.mp hpI
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpr, ?_⟩
      exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr hdp).symm
    -- Step 2: Apply `Stage7SieveMethods.brun_titchmarsh_ap` to every `d ∈ Icc 1 M`
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlogn_gt4 : 4 < Real.log (n : ℝ) := by
      have h81 : Real.exp 4 < (81 : ℝ) := by
        have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have h4 : (Real.exp 1) ^ 4 < 3 ^ 4 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
        rw [← Real.exp_nat_mul] at h4
        norm_num at h4; exact h4
      have hlt : Real.exp 4 < (n : ℝ) := lt_of_lt_of_le h81 (by exact_mod_cast hn)
      exact (Real.log_exp 4).symm.trans_lt (Real.log_lt_log (Real.exp_pos 4) hlt)
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    have hbt_sum :
        ∑ d ∈ Finset.Icc 1 M,
            (((Finset.Ioc 0 (0 + n)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD d])).card : ℝ) ≤
          (20 * (n : ℝ) / Real.log (n : ℝ)) * ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d.totient : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
      have h9d : 9 * d ≤ n := by
        have h1 : 9 * d ≤ M * M := Nat.mul_le_mul hM_ge9 hdM
        exact h1.trans (Nat.sqrt_le n)
      have hbt := Stage7SieveMethods.brun_titchmarsh_ap (by omega : 0 < d) (Nat.coprime_one_left d) 0 n h9d
      have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
      have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
      have hd_le_sqrt : (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
        refine Real.le_sqrt_of_sq_le ?_
        have hnat : d * d ≤ n := (Nat.mul_le_mul hdM hdM).trans (Nat.sqrt_le n)
        rw [sq]; exact_mod_cast hnat
      have hlog_nd_ge : (1 / 2) * Real.log (n : ℝ) ≤ Real.log ((n : ℝ) / (d : ℝ)) := by
        have hge : Real.sqrt (n : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
          rw [le_div_iff₀ hd_pos]
          have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
          nlinarith [Real.sqrt_nonneg (n : ℝ)]
        have h := Real.log_le_log (Real.sqrt_pos.mpr hn_pos) hge
        rw [Real.log_sqrt hn_pos.le] at h
        linarith
      calc (((Finset.Ioc 0 (0 + n)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD d])).card : ℝ)
          ≤ 10 * (n : ℝ) / ((d.totient : ℝ) * Real.log ((n : ℝ) / (d : ℝ))) := hbt
        _ ≤ 10 * (n : ℝ) / ((d.totient : ℝ) * ((1 / 2) * Real.log (n : ℝ))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hlog_nd_ge hphi_pos.le)
        _ = 20 * (n : ℝ) / Real.log (n : ℝ) * (1 / (d.totient : ℝ)) := by
            field_simp [hphi_pos.ne', hlogn_pos.ne']; ring
    -- Step 3: Combine with `sum_inv_totient_le` (`∑_{d=1}^M 1/φ(d) ≤ 3 (log M + 1) ≤ 3 log n`)
    have hlogM_add1 : Real.log (M : ℝ) + 1 ≤ Real.log (n : ℝ) := by
      have hM_le_sqrt : (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
        refine Real.le_sqrt_of_sq_le ?_
        rw [sq]; exact_mod_cast Nat.sqrt_le n
      have h1 : Real.log (M : ℝ) ≤ Real.log (Real.sqrt (n : ℝ)) :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega)) hM_le_sqrt
      rw [Real.log_sqrt hn_pos.le] at h1
      linarith
    have htot_sum : ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d.totient : ℝ) ≤ 3 * Real.log (n : ℝ) :=
      (sum_inv_totient_le hM_ge1).trans (by linarith)
    have hhyperR :
        ((∑ p ∈ P, (Nat.divisors (p - 1)).card : ℕ) : ℝ) ≤
          2 * ∑ d ∈ Finset.Icc 1 M,
            (((Finset.Ioc 0 (0 + n)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD d])).card : ℝ) := by
      exact_mod_cast hhyper
    calc ((∑ p ∈ P, (Nat.divisors (p - 1)).card : ℕ) : ℝ)
        ≤ 2 * ∑ d ∈ Finset.Icc 1 M,
            (((Finset.Ioc 0 (0 + n)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD d])).card : ℝ) := hhyperR
      _ ≤ 2 * ((20 * (n : ℝ) / Real.log (n : ℝ)) *
            ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left hbt_sum (by norm_num)
      _ ≤ 2 * ((20 * (n : ℝ) / Real.log (n : ℝ)) * (3 * Real.log (n : ℝ))) := by gcongr
      _ = 120 * (n : ℝ) := by field_simp [hlogn_pos.ne']; ring

/-- **UNCONDITIONAL TITCHMARSH SHIFTED-PRIME DIVISOR UPPER BOUND (`0` ASSUMPTIONS!)**:
`∃ C > 0, ∀ n : ℕ, ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card ≤ C * n`. -/
theorem titchmarsh_divisor_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        ((∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card : ℕ) : ℝ) ≤
          C * (n : ℝ) :=
  ⟨120, by norm_num, titchmarsh_divisor_upper_bound_explicit⟩

/-! ## Master Unconditional Stage 8 Packaging Theorem -/

/-- **Master Unconditional Stage 8 Theorem (Uniform Non-Exceptional Log-Derivative Bound,
Page's Uniform PNT in AP, Dyadic Non-Exceptional Prime Existence & Titchmarsh Shifted-Prime
Divisor Upper Bound — `0` Assumptions!)**. -/
theorem stage8_uniform_ap_unconditional :
    (∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∃ q₁ : ℕ, (q₁ = 0 ∨ (2 ≤ q₁ ∧ (q₁ : ℝ) ≤ Q)) ∧
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q → (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ s : ℂ, 1 - c' / Real.log (Q * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
                DirichletCharacter.LFunction χ s ≠ 0 ∧
                ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
                  C' * (Real.log (Q * (|s.im| + 2))) ^ 2) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x →
        ∃ q₁ : ℕ,
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ)) →
            (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
                C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 8 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∃ q₁ : ℕ,
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.exp (c * (Real.log x) ^ (1 / 20 : ℝ)) →
            (q₁ = 0 ∨ ¬ q₁ ∣ q) →
            ∀ a : ℕ, Nat.Coprime a q →
              ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x / 2 < (p : ℝ) ∧ (p : ℝ) ≤ x) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        ((∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, (Nat.divisors (p - 1)).card : ℕ) : ℝ) ≤
          C * (n : ℝ)) :=
  ⟨uniform_negLogDerivL_nonexceptional_bound,
   page_uniform_pnt_psiAP,
   exists_prime_in_dyadic_ap_uniform_nonexceptional,
   titchmarsh_divisor_upper_bound⟩

end RHDirect.Stage8UniformAP
