import RHDirect.Interfaces
import RHDirect.ZeroDensityWindow
import RHDirect.Stage2BehrendSieve
import RHDirect.Stage2DirichletAP
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# RHDirect.Stage3BombieriVinogradov

Self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of the
**Additive & Multiplicative Large Sieve Inequalities, Gauss-Sum Modulus Identity, and
Zero-Density Power-Saving / Character-Average Bridges** against `RHDirect.Stage2BehrendSieve`,
`RHDirect.ZeroDensityWindow`, `RHDirect.Stage2DirichletAP`, and targeted Mathlib `v4.33.1`.

## Main Contents
1. **Circle Distance, Additive Character `e(x)`, Geometric Sums & Fejér-Trapezoidal Kernel**:
   - `e x := Complex.exp (2 * π * I * x)`, `distZ x := |x - round x|`, `WellSpaced J α δ`.
   - Exact lower bound `4 * distZ θ ≤ ‖e θ - 1‖` via `Real.mul_le_sin` and geometric-sum bound
     `‖∑_{k < A} e ((M + k) * θ)‖ ≤ (2 * distZ θ)⁻¹`.
   - Trapezoidal Fejér weight `fejerWeight M N L n` (majorizing `1` on `[M, M + N)`) with
     Fourier transform `fejerTransform`: `fejerTransform 0 = N + L` and
     `‖fejerTransform θ‖ ≤ (4 * L * (distZ θ)²)⁻¹`.
   - Well-spaced inverse-square sum bound `∑_{s ∈ J.erase r} (distZ (α s - α r))⁻² ≤ 4 / δ²`
     via injective dyadic-like `(Bool × ℕ)` binning and elementary telescoping `∑_{k=1}^K k⁻² ≤ 2`.
2. **Additive Large Sieve & Farey-Fraction Large Sieve**:
   - `additive_large_sieve_Ico_int`, `additive_large_sieve_Ico_nat`, `additive_large_sieve_Icc`:
     `∑_{r ∈ J} ‖∑_{n = M+1}^{M+N} a_n e(n α_r)‖² ≤ (N + 3 δ⁻¹) ∑ |a_n|²` via
     `Stage2BehrendSieve.gram_large_sieve`.
   - `farey_distZ_ge` (`Q⁻²` spacing of distinct reduced Farey fractions `a/q`, `q ≤ Q`) and
     `farey_large_sieve_Ico`, `farey_large_sieve_Icc`:
     `∑_{q ≤ Q} ∑_{(a,q)=1} ‖S(a/q)‖² ≤ (N + 3 Q²) ∑ |a_n|²`.
3. **Gauss-Sum Modulus `|τ(χ)|² = q` & Multiplicative Large Sieve**:
   - Discrete additive orthogonality and exact Parseval identity for `ZMod.dft`.
   - Exact Gauss-sum modulus identity `norm_sq_gaussSum_eq`: `‖gaussSum χ ZMod.stdAddChar‖² = q`
     for every primitive Dirichlet character `χ mod q` (`q ≥ 1`).
   - Exact primitive-character-to-additive transition identity `gaussSum_mul_char_sum_eq` and
     single-modulus bound `(q / φ(q)) ∑*_{χ mod q} ‖∑ c_n χ(n)‖² ≤ ∑_{(a,q)=1} ‖S(a/q)‖²`.
   - Full **Multiplicative Large Sieve Inequality** (`multiplicative_large_sieve_Ico`,
     `multiplicative_large_sieve_Icc`, `multiplicative_large_sieve_Icc_unweighted`):
     `∑_{q ≤ Q} (q / φ(q)) ∑*_{χ mod q} ‖∑_{n ≤ N} c_n χ(n)‖² ≤ (N + 3 Q²) ∑ |c_n|²`.
4. **Zero-Density Power-Saving & Character-Average Bridges to `ZeroDensityWindow` & `Stage2DirichletAP`**:
   - Multi-modulus bad primitive-character counting (`large_sieve_bad_primitive_chars_card_le`)
     and good-share extraction (`large_sieve_good_primitive_chars_share`) via
     `ZeroDensityWindow.chebyshev_bad_card` & `ZeroDensityWindow.share_of_bad`.
   - Explicit power-saving `Q^(1/100) ≤ Q^(1/4)` bound for dyadic Halász–Montgomery Dirichlet
     polynomials (`dyadic_dirichlet_poly_large_values_power_saving`) and bridge to
     `ZeroDensityWindow.ZeroDensityBoxBound` & `ZeroDensityWindow.count_bad_of_zeroDensityBox`.
   - Unconditional Multiplicative Large Sieve mean-square bound for `Stage2DirichletAP.chebyshevPsiChar`
     (`prim_chebyshevPsiChar_mean_square_le`, `bad_chebyshevPsiChar_card_le`) and exact
     Plancherel / Barban–Davenport–Halberstam AP variance identity (`psiAP_variance_eq_nonprincipal_chars`,
     `psiAP_variance_le`).
-/

noncomputable section

open Complex Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect
namespace Stage3BombieriVinogradov

/-! ## 1. Circle Distance `distZ`, Additive Character `e(x)`, Geometric Sums & Fejér Kernel -/

/-- Additive circle character `e(x) = exp(2 π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- Signed representative of `x mod 1` in `[-1/2, 1/2]`. -/
def fracSym (x : ℝ) : ℝ := x - (round x : ℝ)

/-- Distance from `x : ℝ` to the nearest integer `‖x‖_{ℝ/ℤ} = |x - round x| ∈ [0, 1/2]`. -/
def distZ (x : ℝ) : ℝ := |fracSym x|

/-- A finite family of frequencies `α : κ → ℝ` indexed by `J` is `δ`-well-spaced mod `1`
if `distZ (α r - α s) ≥ δ` for all distinct `r, s ∈ J`. -/
def WellSpaced {κ : Type*} (J : Finset κ) (α : κ → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ distZ (α r - α s)

theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_sub (x y : ℝ) : e (x - y) = e x * e (-y) := by
  rw [sub_eq_add_neg, e_add]

theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  unfold e
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : (2 * Real.pi * Complex.I * (x : ℂ)) = (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem conj_e (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := by
  have h1 : e x * starRingEnd ℂ (e x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]; norm_num
  have h2 : e x * e (-x) = 1 := by
    rw [← e_add, add_neg_cancel, e_zero]
  have hne : e x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem e_int_eq_one (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have h : (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

theorem e_sub_int (x : ℝ) (k : ℤ) : e (x - (k : ℝ)) = e x := by
  rw [e_sub, e_neg, e_int_eq_one, inv_one, mul_one]

theorem e_fracSym (x : ℝ) : e (fracSym x) = e x :=
  e_sub_int x (round x)

theorem distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

theorem distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := abs_sub_round x

theorem distZ_le_abs_sub_int (x : ℝ) (k : ℤ) : distZ x ≤ |x - (k : ℝ)| := by
  unfold distZ fracSym
  by_cases hk : k = round x
  · subst hk; exact le_rfl
  · have h1 : (1 : ℝ) ≤ |(k : ℝ) - (round x : ℝ)| := by
      have hne : k - round x ≠ 0 := sub_ne_zero.mpr hk
      have hnat : (1 : ℤ) ≤ |k - round x| := Int.one_le_abs hne
      exact_mod_cast hnat
    have htri : |(k : ℝ) - (round x : ℝ)| ≤ |x - (round x : ℝ)| + |x - (k : ℝ)| := by
      calc |(k : ℝ) - (round x : ℝ)|
          = |(x - (round x : ℝ)) - (x - (k : ℝ))| := by ring_nf
        _ ≤ |x - (round x : ℝ)| + |x - (k : ℝ)| := abs_sub _ _
    have hhalf : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    linarith

theorem distZ_neg (x : ℝ) : distZ (-x) = distZ x := by
  have h1 : distZ (-x) ≤ distZ x := by
    have h := distZ_le_abs_sub_int (-x) (-round x)
    refine h.trans_eq ?_
    unfold distZ fracSym
    push_cast
    rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) by ring, abs_neg]
  have h2 : distZ x ≤ distZ (-x) := by
    have h := distZ_le_abs_sub_int x (-round (-x))
    refine h.trans_eq ?_
    unfold distZ fracSym
    push_cast
    rw [show x - -(round (-x) : ℝ) = -(-x - (round (-x) : ℝ)) by ring, abs_neg]
  exact le_antisymm h1 h2

theorem distZ_sub_comm (x y : ℝ) : distZ (x - y) = distZ (y - x) := by
  rw [← distZ_neg (x - y), neg_sub]

/-- Exact modulus of `e(x) - 1`: `‖e x - 1‖ = 2 * |sin(π x)|`. -/
theorem norm_e_sub_one_eq (x : ℝ) : ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hfac : e x - 1 = e (x / 2) * (e (x / 2) - e (-(x / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : x / 2 + x / 2 = x := by ring
    have h2 : x / 2 + -(x / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  have hdiff : e (x / 2) - e (-(x / 2)) = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    unfold e
    have hpos : 2 * Real.pi * Complex.I * ((x / 2 : ℝ) : ℂ) = (((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    have hneg : 2 * Real.pi * Complex.I * ((-(x / 2) : ℝ) : ℂ) = (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hfac, norm_mul, norm_e, one_mul, hdiff, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Sharp chord bound on the unit circle: `4 * distZ θ ≤ ‖e θ - 1‖`. -/
theorem four_mul_distZ_le_norm_e_sub_one (θ : ℝ) : 4 * distZ θ ≤ ‖e θ - 1‖ := by
  rw [← e_fracSym θ, norm_e_sub_one_eq]
  have hhalf : |fracSym θ| ≤ 1 / 2 := abs_sub_round θ
  have habs : |Real.sin (Real.pi * fracSym θ)| = Real.sin (Real.pi * distZ θ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    rcases le_total 0 (fracSym θ) with h | h
    · have hd : distZ θ = fracSym θ := by unfold distZ; exact abs_of_nonneg h
      rw [hd]
      have hle : fracSym θ ≤ 1 / 2 := by rwa [abs_of_nonneg h] at hhalf
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hpi.le h) (by nlinarith))
    · have hd : distZ θ = -fracSym θ := by unfold distZ; exact abs_of_nonpos h
      rw [hd, mul_neg, Real.sin_neg]
      have hnn : 0 ≤ -fracSym θ := by linarith
      have hle : -fracSym θ ≤ 1 / 2 := by rwa [abs_of_nonpos h] at hhalf
      have hsin_nn : 0 ≤ Real.sin (Real.pi * (-fracSym θ)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hpi.le hnn) (by nlinarith)
      rw [mul_neg, Real.sin_neg] at hsin_nn
      rw [abs_of_nonpos (by linarith)]
  rw [habs]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hle : Real.pi * distZ θ ≤ Real.pi / 2 := by
    have := distZ_le_half θ
    nlinarith
  have hsin := Real.mul_le_sin (mul_nonneg hpi.le (distZ_nonneg θ)) hle
  have halg : 2 / Real.pi * (Real.pi * distZ θ) = 2 * distZ θ := by
    field_simp [hpi.ne']
  linarith

/-- Telescoping identity for finite geometric exponential sums. -/
private theorem e_sub_one_mul_geom_sum (M : ℤ) (A : ℕ) (θ : ℝ) :
    (e θ - 1) * ∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ) =
      e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hstep : (e θ - 1) * e (((M + (A : ℤ)) : ℤ) * θ) =
        e (((M + ((A + 1 : ℕ) : ℤ)) : ℤ) * θ) - e (((M + (A : ℤ)) : ℤ) * θ) := by
      rw [sub_mul, one_mul, ← e_add]
      congr 1
      congr 1
      push_cast
      ring
    rw [hstep]
    ring

/-- Geometric exponential-sum bound: `‖∑_{k=0}^{A-1} e((M + k) θ)‖ ≤ (2 * distZ θ)⁻¹`
whenever `distZ θ > 0`. -/
theorem norm_geom_sum_e_le (M : ℤ) (A : ℕ) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ (2 * distZ θ)⁻¹ := by
  have h4 : 4 * distZ θ ≤ ‖e θ - 1‖ := four_mul_distZ_le_norm_e_sub_one θ
  have hmul : 4 * distZ θ * ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ 2 := by
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    rw [← norm_mul, e_sub_one_mul_geom_sum]
    calc ‖e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ)‖
        ≤ ‖e (((M + (A : ℤ)) : ℤ) * θ)‖ + ‖e ((M : ℝ) * θ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_e, norm_e]
      _ = 2 := by norm_num
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  linarith

/-- Cleaner direct proof of `norm_geom_sum_e_le` for any `M : ℤ`, `A : ℕ`, and `distZ θ > 0`. -/
theorem norm_geom_sum_e_Ico_le (M : ℤ) (A : ℕ) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ n ∈ Finset.Ico M (M + (A : ℤ)), e ((n : ℝ) * θ)‖ ≤ (2 * distZ θ)⁻¹ := by
  have heq : ∑ n ∈ Finset.Ico M (M + (A : ℤ)), e ((n : ℝ) * θ) =
      ∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ) := by
    refine Finset.sum_bij (fun n _ => (n - M).toNat) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_range]
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ico] at hn₁ hn₂
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨M + (k : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      congr 1
      have hsub : M + ((n - M).toNat : ℤ) = n := by omega
      rw [hsub]
  rw [heq]
  have h4 : 4 * distZ θ ≤ ‖e θ - 1‖ := four_mul_distZ_le_norm_e_sub_one θ
  have hmul : 4 * distZ θ * ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ 2 := by
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    rw [← norm_mul, e_sub_one_mul_geom_sum]
    calc ‖e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ)‖
        ≤ ‖e (((M + (A : ℤ)) : ℤ) * θ)‖ + ‖e ((M : ℝ) * θ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_e, norm_e]
      _ = 2 := by norm_num
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  linarith

/-- Trapezoidal Fejér / de la Vallée Poussin weight supported on `Ico (M - L + 1) (M + N + L)`,
identically equal to `1` on `Ico M (M + N)`. -/
def fejerWeight (M : ℤ) (N L : ℕ) (n : ℤ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ v ∈ Finset.range L,
    if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0

theorem fejerWeight_nonneg (M : ℤ) (N L : ℕ) (n : ℤ) : 0 ≤ fejerWeight M N L n := by
  unfold fejerWeight
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem fejerWeight_eq_one_of_mem {M : ℤ} {N L : ℕ} (hL : 0 < L)
    {n : ℤ} (hn : n ∈ Finset.Ico M (M + (N : ℤ))) :
    fejerWeight M N L n = 1 := by
  simp only [Finset.mem_Ico] at hn
  unfold fejerWeight
  have hsum : ∑ v ∈ Finset.range L,
      (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0) = (L : ℝ) := by
    have hcongr : ∑ v ∈ Finset.range L,
        (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0) =
        ∑ _v ∈ Finset.range L, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_range] at hv
      rw [if_pos ⟨by omega, by omega⟩]
    rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL.ne')]

/-- Exact Fourier transform of the trapezoidal Fejér weight `fejerWeight M N L`. -/
theorem fejerTransform_eq (M : ℤ) (N L : ℕ) (θ : ℝ) :
    ∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
      ((L : ℝ)⁻¹ : ℂ) *
        (∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)) *
        (∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))) := by
  set I' : Finset ℤ := Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ))
  have hexp :
      ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
        ((L : ℝ)⁻¹ : ℂ) * ∑ v ∈ Finset.range L,
          ∑ n ∈ I', (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
            then e ((n : ℝ) * θ) else 0) := by
    have h1 :
        ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
          ((L : ℝ)⁻¹ : ℂ) * ∑ n ∈ I', ∑ v ∈ Finset.range L,
            (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
              then e ((n : ℝ) * θ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold fejerWeight
      rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum, mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
      · rw [if_pos hv, if_pos hv, Complex.ofReal_one, one_mul]
      · rw [if_neg hv, if_neg hv, Complex.ofReal_zero, zero_mul]
    rw [h1, Finset.sum_comm]
  rw [hexp]
  have hinner : ∀ v ∈ Finset.range L,
      ∑ n ∈ I', (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
          then e ((n : ℝ) * θ) else 0) =
        (∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)) * e (-((v : ℝ) * θ)) := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [← Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_bij (fun n _ => n + (v : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
      push_cast
      omega
    · intro n₁ _ n₂ _ h
      omega
    · intro u hu
      simp only [Finset.mem_Ico] at hu
      refine ⟨u - (v : ℤ), ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ico, I']
      push_cast at hu
      omega
    · intro n _
      rw [← e_add]
      congr 1
      push_cast
      ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, mul_assoc]

/-- Diagonal value of the Fejér transform at `θ = 0`: equals `N + L`. -/
theorem fejerTransform_zero (M : ℤ) (N L : ℕ) (hL : 0 < L) :
    ∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * 0) = ((N + L : ℕ) : ℂ) := by
  rw [fejerTransform_eq]
  have h1 : ∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * 0) = ((N + L : ℕ) : ℂ) := by
    simp only [mul_zero, e_zero, Finset.sum_const, Int.card_Ico, add_sub_cancel_left,
      Int.toNat_natCast, nsmul_eq_mul, mul_one]
  have h2 : ∑ v ∈ Finset.range L, e (-((v : ℝ) * 0)) = (L : ℂ) := by
    simp only [mul_zero, neg_zero, e_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [h1, h2]
  have hLne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  push_cast
  field_simp [hLne]

/-- Off-diagonal quadratic decay of the Fejér transform:
`‖fejerTransform θ‖ ≤ (4 * L * (distZ θ)²)⁻¹` for `L > 0` and `distZ θ > 0`. -/
theorem norm_fejerTransform_le (M : ℤ) (N L : ℕ) (hL : 0 < L) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ)‖ ≤
      (4 * (L : ℝ) * distZ θ ^ 2)⁻¹ := by
  rw [fejerTransform_eq, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ‖∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)‖ ≤ (2 * distZ θ)⁻¹ :=
    norm_geom_sum_e_Ico_le M (N + L) hθ
  have h2 : ‖∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))‖ ≤ (2 * distZ θ)⁻¹ := by
    have hrewrite : ∑ v ∈ Finset.range L, e (-((v : ℝ) * θ)) =
        ∑ k ∈ Finset.range L, e (((0 + (k : ℤ)) : ℤ) * (-θ)) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      congr 1; push_cast; ring
    rw [hrewrite]
    have hneg : 0 < distZ (-θ) := by rwa [distZ_neg]
    have hb := norm_geom_sum_e_le 0 L hneg
    rwa [distZ_neg] at hb
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  calc (L : ℝ)⁻¹ * ‖∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)‖ *
        ‖∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))‖
      ≤ (L : ℝ)⁻¹ * (2 * distZ θ)⁻¹ * (2 * distZ θ)⁻¹ := by
        gcongr
    _ = (4 * (L : ℝ) * distZ θ ^ 2)⁻¹ := by
        field_simp [hLpos.ne', hθ.ne']
        ring

/-- Elementary telescoping bound: `∑_{k=1}^K 1 / k² ≤ 2`. -/
private theorem sum_inv_sq_Icc_le_two (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m → ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ ≤ 2 - (m : ℝ)⁻¹ := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hmpos
      · norm_num
      · have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
        rw [hIcc, Finset.sum_insert hnotmem]
        have ihm := ih hmpos
        have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmpos
        have hm1R : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hstep : (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ (m : ℝ)⁻¹ - ((m + 1 : ℕ) : ℝ)⁻¹ := by
          push_cast
          have hdiff : (m : ℝ)⁻¹ - ((m : ℝ) + 1)⁻¹ = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
            field_simp [hmR.ne', (by positivity : (m : ℝ) + 1 ≠ 0)]
            ring
          rw [hdiff, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
        linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · have h := hstrong K hK
    have hinv : (0 : ℝ) ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    linarith

/-- Well-spaced inverse-square sum bound: for any `δ`-well-spaced family `α` on `J` (`δ > 0`)
and any anchor `r ∈ J`, `∑_{s ∈ J.erase r} (distZ (α r - α s))⁻² ≤ 4 / δ²`. -/
theorem sum_inv_distZ_sq_le {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hws : WellSpaced J α δ) {r : κ} (hr : r ∈ J) :
    ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ ≤ 4 / δ ^ 2 := by
  let bin : κ → Bool × ℕ := fun s =>
    (decide (0 ≤ fracSym (α s - α r)), ⌊distZ (α s - α r) / δ⌋₊)
  let K : ℕ := ⌊(1 / 2 : ℝ) / δ⌋₊
  have hinj : Set.InjOn bin (J.erase r : Set κ) := by
    intro s₁ hs₁ s₂ hs₂ hbin
    simp only [Finset.mem_coe, Finset.mem_erase] at hs₁ hs₂
    have hsign : decide (0 ≤ fracSym (α s₁ - α r)) = decide (0 ≤ fracSym (α s₂ - α r)) :=
      congrArg Prod.fst hbin
    have hfl : ⌊distZ (α s₁ - α r) / δ⌋₊ = ⌊distZ (α s₂ - α r) / δ⌋₊ :=
      congrArg Prod.snd hbin
    set k : ℕ := ⌊distZ (α s₁ - α r) / δ⌋₊
    have h1lo : (k : ℝ) ≤ distZ (α s₁ - α r) / δ := Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le)
    have h1hi : distZ (α s₁ - α r) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2lo : (k : ℝ) ≤ distZ (α s₂ - α r) / δ := hfl ▸ Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le)
    have h2hi : distZ (α s₂ - α r) / δ < (k : ℝ) + 1 := hfl ▸ Nat.lt_floor_add_one _
    have habs_diff : |distZ (α s₁ - α r) - distZ (α s₂ - α r)| < δ := by
      have h1a : (k : ℝ) * δ ≤ distZ (α s₁ - α r) := (le_div_iff₀ hδ).mp h1lo
      have h1b : distZ (α s₁ - α r) < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1hi
      have h2a : (k : ℝ) * δ ≤ distZ (α s₂ - α r) := (le_div_iff₀ hδ).mp h2lo
      have h2b : distZ (α s₂ - α r) < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h2hi
      rw [abs_lt]; constructor <;> nlinarith
    have hfrac_diff : |fracSym (α s₁ - α r) - fracSym (α s₂ - α r)| < δ := by
      unfold distZ at habs_diff
      by_cases hp1 : 0 ≤ fracSym (α s₁ - α r)
      · have hp2 : 0 ≤ fracSym (α s₂ - α r) := by
          have : decide (0 ≤ fracSym (α s₂ - α r)) = true := by rw [← hsign, decide_eq_true_eq]; exact hp1
          exact decide_eq_true_eq.mp this
        rwa [abs_of_nonneg hp1, abs_of_nonneg hp2] at habs_diff
      · have hp2 : ¬ 0 ≤ fracSym (α s₂ - α r) := by
          intro h2
          have : decide (0 ≤ fracSym (α s₁ - α r)) = true := by rw [hsign, decide_eq_true_eq]; exact h2
          exact hp1 (decide_eq_true_eq.mp this)
        have hn1 : fracSym (α s₁ - α r) ≤ 0 := le_of_not_ge hp1
        have hn2 : fracSym (α s₂ - α r) ≤ 0 := le_of_not_ge hp2
        rw [abs_of_nonpos hn1, abs_of_nonpos hn2] at habs_diff
        have heq : -(fracSym (α s₁ - α r) - fracSym (α s₂ - α r)) =
            -fracSym (α s₁ - α r) - -fracSym (α s₂ - α r) := by ring
        rw [← abs_neg, heq]
        exact habs_diff
    have hdist_lt : distZ (α s₁ - α s₂) < δ := by
      let m : ℤ := round (α s₁ - α r) - round (α s₂ - α r)
      have hle := distZ_le_abs_sub_int (α s₁ - α s₂) m
      have heq : α s₁ - α s₂ - (m : ℝ) = fracSym (α s₁ - α r) - fracSym (α s₂ - α r) := by
        unfold fracSym; simp only [m]; push_cast; ring
      rw [heq] at hle
      exact lt_of_le_of_lt hle hfrac_diff
    by_contra hne
    have hge := hws s₁ hs₁.2 s₂ hs₂.2 hne
    linarith
  have hmaps : ∀ s ∈ J.erase r, bin s ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K := by
    intro s hs
    simp only [Finset.mem_erase] at hs
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc, bin]
    have hge : δ ≤ distZ (α s - α r) := hws s hs.2 r hr hs.1
    have h1 : 1 ≤ distZ (α s - α r) / δ := (one_le_div hδ).mpr hge
    have h2 : distZ (α s - α r) / δ ≤ (1 / 2 : ℝ) / δ :=
      div_le_div_of_nonneg_right (distZ_le_half _) hδ.le
    exact ⟨Nat.le_floor (by exact_mod_cast h1), Nat.floor_mono h2⟩
  have hterm : ∀ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ ≤ ((((bin s).2 : ℝ) * δ) ^ 2)⁻¹ := by
    intro s hs
    have hk_ge1 : 1 ≤ (bin s).2 := by
      have hmem := hmaps s hs
      simp only [Finset.mem_product, Finset.mem_Icc] at hmem
      exact hmem.2.1
    have hk_pos : (0 : ℝ) < ((bin s).2 : ℝ) * δ := by
      have : (0 : ℝ) < ((bin s).2 : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have hle : ((bin s).2 : ℝ) * δ ≤ distZ (α r - α s) := by
      rw [distZ_sub_comm]
      exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le))
    have hsq : (((bin s).2 : ℝ) * δ) ^ 2 ≤ distZ (α r - α s) ^ 2 :=
      pow_le_pow_left₀ hk_pos.le hle 2
    exact inv_anti₀ (pow_pos hk_pos 2) hsq
  calc ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹
      ≤ ∑ s ∈ J.erase r, ((((bin s).2 : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun s hs => hterm s hs
    _ = ∑ p ∈ (J.erase r).image bin, (((p.2 : ℝ) * δ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun p : Bool × ℕ => (((p.2 : ℝ) * δ) ^ 2)⁻¹) hinj).symm
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K, (((p.2 : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          fun _ _ _ => inv_nonneg.mpr (sq_nonneg _)
    _ = ∑ _b : Bool, ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_product _ _ _
    _ = 2 * (δ ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, mul_inv, mul_comm ((k : ℝ) ^ 2)⁻¹]
    _ ≤ 2 * (δ ^ 2)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le_two K) (by positivity)
    _ = 4 / δ ^ 2 := by ring

/-! ## 2. Additive Large Sieve & Farey-Fraction Large Sieve -/

/-- **Additive Large Sieve Inequality (integer interval `Ico M (M + N)`)**:
for any `δ`-well-spaced frequencies `α : κ → ℝ` (`δ > 0`) on a finite set `J`, any `M : ℤ`,
`N : ℕ`, and any complex coefficients `a : ℤ → ℂ`,
`∑_{r ∈ J} ‖∑_{n ∈ Ico M (M + N)} a n * e (n * α r)‖² ≤ (N + 3 * δ⁻¹) * ∑_{n ∈ Ico M (M + N)} ‖a n‖²`. -/
theorem additive_large_sieve_Ico_int {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hws : WellSpaced J α δ) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
      ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
  by_cases hδ_half : 1 / 2 < δ
  · -- When `δ > 1/2`, `J` has at most one element since `distZ ≤ 1/2`.
    have hcard : J.card ≤ 1 := by
      refine Finset.card_le_one.mpr fun r hr s hs => ?_
      by_contra hne
      linarith [hws r hr s hs hne, distZ_le_half (α r - α s)]
    have hterm : ∀ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
        (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
      intro r _
      have hcs := Stage2BehrendSieve.cauchy_schwarz_complex_card
        (Finset.Ico M (M + (N : ℤ))) (fun n => a n * e ((n : ℝ) * α r))
      have hcardI : ((Finset.Ico M (M + (N : ℤ))).card : ℝ) = (N : ℝ) := by
        simp [Int.card_Ico]
      have hnorm : ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n * e ((n : ℝ) * α r)‖ ^ 2 =
          ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, norm_e, mul_one]
      rw [hcardI, hnorm] at hcs
      exact hcs
    calc ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2
        ≤ ∑ _r ∈ J, (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (J.card : ℝ) * ((N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * ((N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ?_
          exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := one_mul _
      _ ≤ ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith [inv_pos.mpr hδ])
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · -- Main regime `0 < δ ≤ 1/2`: apply `gram_large_sieve` with the trapezoidal Fejér weight
    -- `w = fejerWeight M N L` at `L = ⌈δ⁻¹⌉₊`.
    have hδ_le : δ ≤ 1 / 2 := le_of_not_gt hδ_half
    set L : ℕ := ⌈δ⁻¹⌉₊
    have hinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hL_ge : δ⁻¹ ≤ (L : ℝ) := Nat.le_ceil δ⁻¹
    have hL_pos : 0 < L := by
      have : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le hinv_pos hL_ge
      exact Nat.cast_pos.mp this
    have hL_le : (L : ℝ) ≤ 2 * δ⁻¹ := by
      have hlt := Nat.ceil_lt_add_one hinv_pos.le
      have h1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
      linarith
    set I : Finset ℤ := Finset.Ico M (M + (N : ℤ))
    set I' : Finset ℤ := Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ))
    have hI_sub : I ⊆ I' := fun n hn => by
      simp only [Finset.mem_Ico, I, I'] at hn ⊢
      omega
    let K : κ → ℤ → ℂ := fun r n => ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e ((n : ℝ) * α r)
    let a' : ℤ → ℂ := fun n => if n ∈ I then a n else 0
    have hΔ0 : 0 ≤ (N : ℝ) + 3 * δ⁻¹ := by positivity
    have hGram : ∀ r ∈ J, ∑ s ∈ J, ‖∑ n ∈ I', K r n * starRingEnd ℂ (K s n)‖ ≤ (N : ℝ) + 3 * δ⁻¹ := by
      intro r hr
      have hGeq : ∀ s : κ, ∑ n ∈ I', K r n * starRingEnd ℂ (K s n) =
          ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s)) := by
        intro s
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [K]
        rw [map_mul, Complex.conj_ofReal, conj_e]
        have hsq : ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) *
            ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) = ((fejerWeight M N L n : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (fejerWeight_nonneg M N L n)]
        calc ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e ((n : ℝ) * α r) *
              (((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e (-((n : ℝ) * α s)))
            = (((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) *
                ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ)) *
                (e ((n : ℝ) * α r) * e (-((n : ℝ) * α s))) := by ring
          _ = ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s)) := by
              rw [hsq, ← e_add]; congr 2; ring
      simp_rw [hGeq]
      rw [← Finset.add_sum_erase J _ hr]
      have hdiag : ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α r))‖ =
          (N : ℝ) + (L : ℝ) := by
        rw [sub_self, fejerTransform_zero M N L hL_pos]
        rw [show ((N + L : ℕ) : ℂ) = (((N : ℝ) + (L : ℝ) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hoff : ∑ s ∈ J.erase r,
          ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s))‖ ≤ δ⁻¹ := by
        have hLposR : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
        calc ∑ s ∈ J.erase r,
              ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s))‖
            ≤ ∑ s ∈ J.erase r, (4 * (L : ℝ) * distZ (α r - α s) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun s hs => ?_
              have hne : r ≠ s := (Finset.mem_erase.mp hs).1.symm
              have hds : 0 < distZ (α r - α s) := lt_of_lt_of_le hδ (hws r hr s (Finset.mem_erase.mp hs).2 hne)
              exact norm_fejerTransform_le M N L hL_pos hds
          _ = (4 * (L : ℝ))⁻¹ * ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [mul_inv]
          _ ≤ (4 * (L : ℝ))⁻¹ * (4 / δ ^ 2) :=
              mul_le_mul_of_nonneg_left (sum_inv_distZ_sq_le J α hδ hws hr) (by positivity)
          _ = ((L : ℝ) * δ ^ 2)⁻¹ := by
              field_simp [hLposR.ne', hδ.ne']
          _ ≤ δ⁻¹ := by
              rw [inv_le_inv₀ (by positivity) hδ]
              have h1 : 1 ≤ (L : ℝ) * δ := by
                have := mul_le_mul_of_nonneg_right hL_ge hδ.le
                rwa [inv_mul_cancel₀ hδ.ne'] at this
              nlinarith
      rw [hdiag]
      linarith
    have hLS := Stage2BehrendSieve.gram_large_sieve I' J K hΔ0 hGram a'
    have hLHS : ∑ r ∈ J, ‖∑ n ∈ I', K r n * a' n‖ ^ 2 =
        ∑ r ∈ J, ‖∑ n ∈ I, a n * e ((n : ℝ) * α r)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 2
      rw [← Finset.sum_subset hI_sub]
      · refine Finset.sum_congr rfl fun n hn => ?_
        dsimp only [K, a']
        rw [if_pos hn, fejerWeight_eq_one_of_mem hL_pos hn, Real.sqrt_one, Complex.ofReal_one, one_mul, mul_comm]
      · intro n _ hn
        dsimp only [a']
        rw [if_neg hn, mul_zero]
    have hRHS : ∑ n ∈ I', ‖a' n‖ ^ 2 = ∑ n ∈ I, ‖a n‖ ^ 2 := by
      rw [← Finset.sum_subset hI_sub]
      · refine Finset.sum_congr rfl fun n hn => ?_
        dsimp only [a']; rw [if_pos hn]
      · intro n _ hn
        dsimp only [a']; rw [if_neg hn, norm_zero, zero_pow (by norm_num)]
    rw [hLHS, hRHS] at hLS
    exact hLS

/-- **Additive Large Sieve Inequality on `ℕ` (`Finset.Ico M (M + N)`)**. -/
theorem additive_large_sieve_Ico_nat {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hws : WellSpaced J α δ) (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + N), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
      ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by
  let aZ : ℤ → ℂ := fun z => if 0 ≤ z then a z.toNat else 0
  have h := additive_large_sieve_Ico_int J α hδ hws (M : ℤ) N aZ
  have hL : ∀ r : κ,
      ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + (N : ℤ)), aZ n * e ((n : ℝ) * α r) =
        ∑ n ∈ Finset.Ico M (M + N), a n * e ((n : ℝ) * α r) := by
    intro r
    refine Finset.sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_Ico] at hz ⊢; omega
    · intro z₁ hz₁ z₂ hz₂ heq; simp only [Finset.mem_Ico] at hz₁ hz₂; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn
      exact ⟨(n : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro z hz
      simp only [Finset.mem_Ico] at hz
      have hz0 : 0 ≤ z := by omega
      dsimp only [aZ]
      rw [if_pos hz0]
      have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hz0
      rw [hcast]
  have hR : ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + (N : ℤ)), ‖aZ n‖ ^ 2 =
      ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by
    refine Finset.sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_Ico] at hz ⊢; omega
    · intro z₁ hz₁ z₂ hz₂ heq; simp only [Finset.mem_Ico] at hz₁ hz₂; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn
      exact ⟨(n : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro z hz
      simp only [Finset.mem_Ico] at hz
      dsimp only [aZ]; rw [if_pos (by omega)]
  simp_rw [hL] at h
  rw [hR] at h
  exact h

/-- **Additive Large Sieve Inequality on `Finset.Icc (M + 1) (M + N)`**. -/
theorem additive_large_sieve_Icc {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hws : WellSpaced J α δ) (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ J, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
      ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  have heq : Finset.Icc (M + 1) (M + N) = Finset.Ico (M + 1) ((M + 1) + N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [heq]
  exact additive_large_sieve_Ico_nat J α hδ hws (M + 1) N a

/-- Reduced Farey fractions `(q, a)` with `1 ≤ q ≤ Q`, `a < q`, and `Nat.Coprime a q`. -/
def fareyPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => (q, a))

/-- Distinct reduced Farey fractions of denominator `≤ Q` are `Q⁻²`-well-spaced mod `1`. -/
theorem farey_distZ_ge {Q : ℕ} (hQ : 0 < Q) :
    WellSpaced (fareyPairs Q) (fun p => (p.2 : ℝ) / (p.1 : ℝ)) (((Q : ℝ) ^ 2)⁻¹) := by
  intro p₁ hp₁ p₂ hp₂ hne
  simp only [fareyPairs, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range] at hp₁ hp₂
  obtain ⟨q₁, ⟨hq1_lo, hq1_hi⟩, a₁, ⟨ha1_lt, hcop1⟩, rfl⟩ := hp₁
  obtain ⟨q₂, ⟨hq2_lo, hq2_hi⟩, a₂, ⟨ha2_lt, hcop2⟩, rfl⟩ := hp₂
  have hq1_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq2_pos : (0 : ℝ) < (q₂ : ℝ) := Nat.cast_pos.mpr (by omega)
  let k : ℤ := round ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ))
  let m : ℤ := (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) - k * (q₁ : ℤ) * (q₂ : ℤ)
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hdiv1 : (q₁ : ℤ) ∣ (a₁ : ℤ) * (q₂ : ℤ) := by
      refine ⟨(a₂ : ℤ) + k * (q₂ : ℤ), ?_⟩
      dsimp only [m] at hm0
      linarith
    have hdiv2 : (q₂ : ℤ) ∣ (a₂ : ℤ) * (q₁ : ℤ) := by
      refine ⟨(a₁ : ℤ) - k * (q₁ : ℤ), ?_⟩
      dsimp only [m] at hm0
      linarith
    have hnat1 : q₁ ∣ a₁ * q₂ := Int.natCast_dvd_natCast.mp (by simpa using hdiv1)
    have hnat2 : q₂ ∣ a₂ * q₁ := Int.natCast_dvd_natCast.mp (by simpa using hdiv2)
    have hq12 : q₁ ∣ q₂ := hcop1.symm.dvd_of_dvd_mul_left hnat1
    have hq21 : q₂ ∣ q₁ := hcop2.symm.dvd_of_dvd_mul_left hnat2
    have hqeq : q₁ = q₂ := Nat.dvd_antisymm hq12 hq21
    subst hqeq
    have hdiff : ((a₁ : ℤ) - (a₂ : ℤ) - k * (q₁ : ℤ)) * (q₁ : ℤ) = 0 := by
      dsimp only [m] at hm0
      linarith
    have hsub : (a₁ : ℤ) - (a₂ : ℤ) = k * (q₁ : ℤ) := by
      have hqne : (q₁ : ℤ) ≠ 0 := by omega
      have := (mul_eq_zero.mp hdiff).resolve_right hqne
      linarith
    have hk0 : k = 0 := by
      by_contra hk
      have habs : (q₁ : ℤ) ≤ |k * (q₁ : ℤ)| := by
        rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (q₁ : ℤ))]
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
        nlinarith
      rw [← hsub] at habs
      have : |(a₁ : ℤ) - (a₂ : ℤ)| < (q₁ : ℤ) := by
        rw [abs_lt]; omega
      omega
    have haeq : a₁ = a₂ := by rw [hk0, zero_mul] at hsub; omega
    exact hne (Prod.ext rfl haeq)
  have hm_ge : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    exact_mod_cast this
  have hval : fracSym ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)) = (m : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    unfold fracSym
    dsimp only [m, k]
    push_cast
    field_simp [hq1_pos.ne', hq2_pos.ne']
  have hdist : distZ ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)) = |(m : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    unfold distZ
    rw [hval, abs_div, abs_of_pos (mul_pos hq1_pos hq2_pos)]
  rw [hdist]
  have hqq : (q₁ : ℝ) * (q₂ : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq1_hi
    have h2 : (q₂ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq2_hi
    nlinarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  calc ((Q : ℝ) ^ 2)⁻¹
      = 1 / (Q : ℝ) ^ 2 := by rw [one_div]
    _ ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := one_div_le_one_div_of_le (mul_pos hq1_pos hq2_pos) hqq
    _ ≤ |(m : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := div_le_div_of_nonneg_right hm_ge (mul_pos hq1_pos hq2_pos).le

private theorem sum_fareyPairs_eq (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ fareyPairs Q, f p.1 p.2 =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f q a := by
  unfold fareyPairs
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_image]
    intro a₁ _ a₂ _ h
    exact (Prod.mk.inj h).2
  · intro q₁ _ q₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image] at hp1 hp2
    obtain ⟨a₁, _, rfl⟩ := hp1
    obtain ⟨a₂, _, h2⟩ := hp2
    exact hne (Prod.mk.inj h2).1.symm

/-- **Farey-Fraction Large Sieve Inequality (`Finset.Ico M (M + N)`)**:
`∑_{q=1}^Q ∑_{a < q, (a,q)=1} ‖∑_{n ∈ Ico M (M + N)} c n * e(n a / q)‖² ≤ (N + 3 Q²) ∑ ‖c n‖²`. -/
theorem farey_large_sieve_Ico (Q M N : ℕ) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + N), ‖c n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hδ : 0 < ((Q : ℝ) ^ 2)⁻¹ := inv_pos.mpr (pow_pos (Nat.cast_pos.mpr hQ) 2)
    have h := additive_large_sieve_Ico_nat (fareyPairs Q) (fun p => (p.2 : ℝ) / (p.1 : ℝ))
      hδ (farey_distZ_ge hQ) M N c
    rw [inv_inv, sum_fareyPairs_eq (f := fun q a =>
      ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2)] at h
    exact h

/-- **Farey-Fraction Large Sieve Inequality (`Finset.Icc 1 N`)**:
`∑_{q=1}^Q ∑_{a < q, (a,q)=1} ‖∑_{n=1}^N c n * e(n a / q)‖² ≤ (N + 3 Q²) ∑_{n=1}^N ‖c n‖²`. -/
theorem farey_large_sieve_Icc (Q N : ℕ) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∑ n ∈ Finset.Icc 1 N, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have heq : Finset.Icc 1 N = Finset.Ico 1 (1 + N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [heq]
  exact farey_large_sieve_Ico Q 1 N c

/-! ## 3. Gauss-Sum Modulus Identity `|τ(χ)|² = q` & Multiplicative Large Sieve -/

/-- Exact evaluation of `ZMod.stdAddChar` in terms of `e`: `stdAddChar (a : ZMod q) = e (a.val / q)`. -/
theorem stdAddChar_eq_e {q : ℕ} [NeZero q] (a : ZMod q) :
    ZMod.stdAddChar a = e ((a.val : ℝ) / (q : ℝ)) := by
  have hcast : (((a.val : ℤ) : ZMod q)) = a := by simp
  conv_lhs => rw [← hcast]
  rw [ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

theorem stdAddChar_natCast_eq_e {q : ℕ} [NeZero q] (m : ℕ) :
    ZMod.stdAddChar (m : ZMod q) = e ((m : ℝ) / (q : ℝ)) := by
  have h := ZMod.stdAddChar_coe (N := q) (m : ℤ)
  push_cast at h
  rw [h]
  unfold e
  congr 1
  push_cast
  ring

theorem norm_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [stdAddChar_eq_e, norm_e]

theorem conj_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  have h1 : ZMod.stdAddChar a * starRingEnd ℂ (ZMod.stdAddChar a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_stdAddChar]; norm_num
  have h2 : ZMod.stdAddChar a * ZMod.stdAddChar (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hne : ZMod.stdAddChar a ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem stdAddChar_ne_one_of_ne_zero {q : ℕ} [NeZero q] {d : ZMod q} (hd : d ≠ 0) :
    ZMod.stdAddChar d ≠ 1 := by
  rw [stdAddChar_eq_e]
  have hval_pos : 0 < d.val := Nat.pos_of_ne_zero fun h0 => hd (by rw [← ZMod.natCast_zmod_val d, h0, Nat.cast_zero])
  have hval_lt : d.val < q := ZMod.val_lt d
  have hdist_pos : 0 < distZ ((d.val : ℝ) / (q : ℝ)) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have h0 : (0 : ℝ) < (d.val : ℝ) / (q : ℝ) := div_pos (Nat.cast_pos.mpr hval_pos) hq_pos
    have h1 : (d.val : ℝ) / (q : ℝ) < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast hval_lt)
    unfold distZ fracSym
    rw [abs_pos]
    intro heq
    have hint : (d.val : ℝ) / (q : ℝ) = (round ((d.val : ℝ) / (q : ℝ)) : ℝ) := sub_eq_zero.mp heq
    have hk0 : (0 : ℤ) < round ((d.val : ℝ) / (q : ℝ)) := by
      have : ((0 : ℤ) : ℝ) < (round ((d.val : ℝ) / (q : ℝ)) : ℝ) := by rw [← hint]; simpa using h0
      exact_mod_cast this
    have hk1 : round ((d.val : ℝ) / (q : ℝ)) < 1 := by
      have : (round ((d.val : ℝ) / (q : ℝ)) : ℝ) < ((1 : ℤ) : ℝ) := by rw [← hint]; simpa using h1
      exact_mod_cast this
    omega
  intro heq
  have h4 := four_mul_distZ_le_norm_e_sub_one ((d.val : ℝ) / (q : ℝ))
  rw [heq, sub_self, norm_zero] at h4
  linarith

/-- Additive character orthogonality on `ZMod q`. -/
theorem sum_stdAddChar_mul {q : ℕ} [NeZero q] (d : ZMod q) :
    ∑ k : ZMod q, ZMod.stdAddChar (k * d) = if d = 0 then (q : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one, ite_true]
  · rw [if_neg hd]
    set S : ℂ := ∑ k : ZMod q, ZMod.stdAddChar (k * d)
    have hshift : ZMod.stdAddChar d * S = S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      calc ∑ k : ZMod q, ZMod.stdAddChar d * ZMod.stdAddChar (k * d)
          = ∑ k : ZMod q, ZMod.stdAddChar ((k + 1) * d) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← AddChar.map_add_eq_mul]; congr 1; ring
        _ = ∑ k : ZMod q, ZMod.stdAddChar (k * d) := by
            exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod q)) _ _ fun k => rfl
    have hmul : (ZMod.stdAddChar d - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (stdAddChar_ne_one_of_ne_zero hd))

/-- Exact discrete Parseval / Plancherel identity for `ZMod.dft`. -/
theorem zmod_dft_parseval {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) :
    ∑ k : ZMod q, ‖ZMod.dft Φ k‖ ^ 2 = (q : ℝ) * ∑ j : ZMod q, ‖Φ j‖ ^ 2 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hsq]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]
  congr 1
  have hL : ∑ k : ZMod q, ZMod.dft Φ k * starRingEnd ℂ (ZMod.dft Φ k) =
      ∑ j : ZMod q, ∑ j' : ZMod q,
        Φ j * starRingEnd ℂ (Φ j') * ∑ k : ZMod q, ZMod.stdAddChar (k * (j' - j)) := by
    have hexp : ∀ k : ZMod q,
        ZMod.dft Φ k * starRingEnd ℂ (ZMod.dft Φ k) =
          ∑ j : ZMod q, ∑ j' : ZMod q,
            Φ j * starRingEnd ℂ (Φ j') * ZMod.stdAddChar (k * (j' - j)) := by
      intro k
      rw [ZMod.dft_def]
      simp only [smul_eq_mul, map_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [map_mul, conj_stdAddChar, neg_neg]
      have hadd : ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) =
          ZMod.stdAddChar (k * (j' - j)) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      calc ZMod.stdAddChar (-(j * k)) * Φ j * (ZMod.stdAddChar (j' * k) * starRingEnd ℂ (Φ j'))
          = Φ j * starRingEnd ℂ (Φ j') * (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k)) := by ring
        _ = Φ j * starRingEnd ℂ (Φ j') * ZMod.stdAddChar (k * (j' - j)) := by rw [hadd]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [sum_stdAddChar_mul]
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl]; ring
  · intro j' _ hne
    rw [if_neg (sub_ne_zero.mpr hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Sum of squared norms of any Dirichlet character over `ZMod q` equals `φ(q)`. -/
private theorem sum_norm_sq_dirichletChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ j : ZMod q, ‖χ j‖ ^ 2 = (Nat.totient q : ℝ) := by
  have hfilt : ∑ j : ZMod q, ‖χ j‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j : ZMod q => IsUnit j), (1 : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : IsUnit j
    · rw [if_pos hj, (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ hj).1, one_pow]
    · rw [if_neg hj, MulChar.map_nonunit χ hj, norm_zero, zero_pow (by norm_num)]
  rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun j : ZMod q => IsUnit j)).card = Fintype.card (ZMod q)ˣ := by
    refine Finset.card_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q)) ?_ ?_ ?_ |>.symm
    · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
    · intro u₁ _ u₂ _ h; exact Units.ext h
    · intro j hj
      obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hj).2
      exact ⟨u, Finset.mem_univ _, rfl⟩
  rw [hcard, ZMod.card_units_eq_totient]

/-- **Gauss-Sum Modulus Identity**: for every primitive Dirichlet character `χ mod q` (`q ≥ 1`),
`‖gaussSum χ ZMod.stdAddChar‖² = q` and `‖gaussSum χ ZMod.stdAddChar‖ = √q`. -/
theorem norm_sq_gaussSum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  have hp := zmod_dft_parseval (Φ := (χ : ZMod q → ℂ))
  rw [sum_norm_sq_dirichletChar χ] at hp
  have hL : ∑ k : ZMod q, ‖ZMod.dft (⇑χ) k‖ ^ 2 =
      ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * (Nat.totient q : ℝ) := by
    have h1 : ∀ k : ZMod q, ‖ZMod.dft (⇑χ) k‖ ^ 2 =
        ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ‖χ⁻¹ (-k)‖ ^ 2 := by
      intro k
      rw [hprim.fourierTransform_eq_inv_mul_gaussSum k, norm_mul, mul_pow, mul_comm]
    simp_rw [h1, ← Finset.mul_sum]
    congr 1
    calc ∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2
        = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
          Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ fun _ => rfl
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletChar χ⁻¹
  rw [hL] at hp
  have hphi : (Nat.totient q : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  exact mul_right_cancel₀ hphi hp

theorem norm_gaussSum_eq_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_gaussSum_eq hprim]

/-- Exact Gauss-sum multiplicative-to-additive transition identity for any primitive `χ mod q`:
`τ(χ⁻¹) * ∑_{n ∈ I} c n * χ(n) = ∑_{a ∈ (ZMod q)ˣ} χ⁻¹(a) * ∑_{n ∈ I} c n * e(n * a.val / q)`. -/
theorem gaussSum_mul_char_sum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (I : Finset ℕ) (c : ℕ → ℂ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ I, c n * χ (n : ZMod q) =
      ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
        ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hpoint : ∀ n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q) =
      ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
    intro n
    have hft := hprim_inv.fourierTransform_eq_inv_mul_gaussSum (-(n : ZMod q))
    rw [inv_inv, neg_neg, mul_comm] at hft
    rw [← hft, ZMod.dft_def]
    simp only [smul_eq_mul]
    have hfilt : ∑ j : ZMod q, ZMod.stdAddChar (-(j * -(n : ZMod q))) * χ⁻¹ j =
        ∑ j ∈ Finset.univ.filter (fun j : ZMod q => IsUnit j),
          ZMod.stdAddChar (j * (n : ZMod q)) * χ⁻¹ j := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : IsUnit j
      · rw [if_pos hj, mul_neg, neg_neg]
      · rw [if_neg hj, MulChar.map_nonunit χ⁻¹ hj, mul_zero]
    rw [hfilt]
    refine Finset.sum_bij (fun j hj => (Finset.mem_filter.mp hj).2.unit) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro j₁ hj₁ j₂ hj₂ h
      have := congrArg Units.val h
      simpa using this
    · intro a _
      exact ⟨(a : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩, Units.ext (by simp)⟩
    · intro j hj
      have hjval : (((Finset.mem_filter.mp hj).2.unit : (ZMod q)ˣ) : ZMod q) = j := by simp
      rw [hjval, mul_comm]
      congr 1
      have hmul : (j : ZMod q) * (n : ZMod q) = ((n * j.val : ℕ) : ZMod q) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]
      rw [hmul, stdAddChar_natCast_eq_e]
      congr 1
      push_cast
      ring
  calc gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ I, c n * χ (n : ZMod q)
      = ∑ n ∈ I, c n * (gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ n ∈ I, c n * ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
        refine Finset.sum_congr rfl fun n _ => by rw [hpoint n]
    _ = ∑ n ∈ I, ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          (c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum I _ _).symm

/-- Exact character Parseval on `(ZMod q)ˣ`:
`∑_{χ mod q} ‖∑_{a : (ZMod q)ˣ} χ⁻¹(a) * S(a)‖² = φ(q) * ∑_{a : (ZMod q)ˣ} ‖S(a)‖²`. -/
private theorem sum_all_chars_units_parseval {q : ℕ} [NeZero q] (S : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hsq]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]
  congr 1
  have hinv : ∑ χ : DirichletCharacter ℂ q,
      (∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a) *
        starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a) =
      ∑ χ : DirichletCharacter ℂ q,
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
        starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) :=
    Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ fun _ => rfl
  rw [hinv]
  have hexp :
      ∑ χ : DirichletCharacter ℂ q,
          (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
            starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) =
        ∑ a : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ,
          S a * starRingEnd ℂ (S b) *
            ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q)) := by
    have h1 : ∀ χ : DirichletCharacter ℂ q,
        (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
          starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) =
        ∑ a : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ,
          S a * starRingEnd ℂ (S b) * (χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q))) := by
      intro χ
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Stage2BehrendSieve.dirichlet_orthogonality_conj]
  rw [Finset.sum_eq_single a]
  · rw [if_pos ⟨a.isUnit, rfl⟩]; ring
  · intro b _ hne
    rw [if_neg (fun h => hne (Units.ext h.2.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

open Classical in
/-- **Single-Modulus Primitive-Character to Additive-Sum Transition Inequality**:
for any `q ≥ 1`, finite `I : Finset ℕ`, and `c : ℕ → ℂ`,
`(q / φ(q)) * ∑*_{χ mod q} ‖∑_{n ∈ I} c n * χ(n)‖² ≤ ∑_{a < q, (a,q)=1} ‖∑_{n ∈ I} c n * e(n a / q)‖²`. -/
theorem primitive_char_sum_le_additive_sum {q : ℕ} [NeZero q] (I : Finset ℕ) (c : ℕ → ℂ) :
    ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ I, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  let S : (ZMod q)ˣ → ℂ := fun a =>
    ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))
  have hq_lhs :
      (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 =
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
    have hprim_inv : χ⁻¹.IsPrimitive := by
      show χ⁻¹.conductor = q
      rw [DirichletCharacter.conductor_inv, hprim]
    rw [← norm_sq_gaussSum_eq hprim_inv, ← mul_pow, ← norm_mul,
      gaussSum_mul_char_sum_eq hprim I c]
  have hle_all :
      (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 ≤
        (Nat.totient q : ℝ) * ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 := by
    rw [hq_lhs, ← sum_all_chars_units_parseval S]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hbij : ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ I, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
    · intro u _
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      have hu : IsUnit (((u : ZMod q).val : ℕ) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]; exact u.isUnit
      exact (ZMod.isUnit_iff_coprime _ q).mp hu
    · intro u₁ _ u₂ _ h
      exact Units.ext (by rw [← ZMod.natCast_zmod_val (u₁ : ZMod q), ← ZMod.natCast_zmod_val (u₂ : ZMod q), h])
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha.2
      refine ⟨hu.unit, Finset.mem_univ _, ?_⟩
      simp only [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
    · intro u _; rfl
  rw [hbij] at hle_all
  rw [div_mul_eq_mul_div, div_le_iff₀ hphi_pos]
  linarith

open Classical in
/-- **Multiplicative Large Sieve Inequality (`Finset.Ico M (M + N)`)**:
averaged over all primitive Dirichlet characters `χ mod (k + 1)` with `0 ≤ k < Q` (i.e. `1 ≤ q ≤ Q`),
`∑_{q=1}^Q (q / φ(q)) ∑*_{χ mod q} ‖∑_{n ∈ Ico M (M + N)} c n * χ(n)‖² ≤ (N + 3 Q²) ∑ ‖c n‖²`. -/
theorem multiplicative_large_sieve_Ico (Q M N : ℕ) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + N), ‖c n‖ ^ 2 := by
  have hstep :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ico M (M + N), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
        ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 :=
    Finset.sum_le_sum fun k _ =>
      primitive_char_sum_le_additive_sum (q := k + 1) (Finset.Ico M (M + N)) c
  have hshift :
      ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k₁ _ k₂ _ h; omega
    · intro q hq; rw [Finset.mem_Icc] at hq
      exact ⟨q - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  exact hstep.trans (hshift ▸ farey_large_sieve_Ico Q M N c)

open Classical in
/-- **Multiplicative Large Sieve Inequality (`Finset.Icc 1 N`, canonical `k + 1` indexing)**:
`∑_{k ∈ range Q} ((k+1) / φ(k+1)) ∑*_{χ mod (k+1)} ‖∑_{n=1}^N c n * χ(n)‖² ≤ (N + 3 Q²) ∑_{n=1}^N ‖c n‖²`. -/
theorem multiplicative_large_sieve_Icc (Q N : ℕ) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Icc 1 N, c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have hstep :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Icc 1 N, c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
        ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Icc 1 N, c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 := by
    refine Finset.sum_le_sum fun k _ => ?_
    exact primitive_char_sum_le_additive_sum (q := k + 1) (Finset.Icc 1 N) c
  have hshift :
      ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Icc 1 N, c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ‖∑ n ∈ Finset.Icc 1 N, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k₁ _ k₂ _ h; omega
    · intro q hq; rw [Finset.mem_Icc] at hq
      exact ⟨q - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  exact hstep.trans (hshift ▸ farey_large_sieve_Icc Q N c)

open Classical in
/-- Unweighted **Multiplicative Large Sieve Inequality** over primitive characters `q ≤ Q`
(dropping the weight `q / φ(q) ≥ 1`). -/
theorem multiplicative_large_sieve_Icc_unweighted (Q N : ℕ) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc 1 N, c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  refine (Finset.sum_le_sum fun k _ => ?_).trans (multiplicative_large_sieve_Icc Q N c)
  have hge1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ) := by
    rw [one_le_div (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k)))]
    exact_mod_cast Nat.totient_le (k + 1)
  have hnn : 0 ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
      ‖∑ n ∈ Finset.Icc 1 N, c n * χ (n : ZMod (k + 1))‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hge1 hnn

open Classical in
/-- Unweighted **Multiplicative Large Sieve Inequality** on an arbitrary interval `Finset.Icc M₁ M₂`. -/
theorem multiplicative_large_sieve_Icc_range (Q M₁ M₂ : ℕ) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc M₁ M₂, c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      (((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2 := by
  by_cases hle : M₁ ≤ M₂
  · have hIco : Finset.Icc M₁ M₂ = Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIco]
    have h1 :
        ∑ k ∈ Finset.range Q,
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
          ∑ k ∈ Finset.range Q,
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod (k + 1))‖ ^ 2 := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hge1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ) := by
        rw [one_le_div (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k)))]
        exact_mod_cast Nat.totient_le (k + 1)
      have hnn : 0 ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod (k + 1))‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hge1 hnn
    have h2 :
        ∑ k ∈ Finset.range Q,
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
          ∑ k ∈ Finset.range Q,
            ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
              ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 :=
      Finset.sum_le_sum fun k _ =>
        primitive_char_sum_le_additive_sum (q := k + 1) (Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁))) c
    have hshift :
        ∑ k ∈ Finset.range Q,
            ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
              ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 =
          ∑ q ∈ Finset.Icc 1 Q,
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ‖∑ n ∈ Finset.Ico M₁ (M₁ + (M₂ + 1 - M₁)), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro k₁ _ k₂ _ h; omega
      · intro q hq; rw [Finset.mem_Icc] at hq
        exact ⟨q - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k _; rfl
    exact (h1.trans h2).trans (hshift ▸ farey_large_sieve_Ico Q M₁ (M₂ + 1 - M₁) c)
  · have hempty : Finset.Icc M₁ M₂ = ∅ := Finset.Icc_eq_empty hle
    rw [hempty]
    simp

/-! ## 4. Zero-Density Power-Saving & Character-Average Bridges to `ZeroDensityWindow` & `Stage2DirichletAP` -/

open Classical in
/-- The finite family of all primitive Dirichlet characters of conductor `≤ Q`, indexed in the
exact `Σ k : ℕ, DirichletCharacter ℂ (k + 1)` type of `ZeroDensityWindow.ZeroDensityBoxBound`. -/
def primCharsUpTo (Q : ℕ) : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
  (Finset.range Q).sigma fun k =>
    Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive

theorem mem_primCharsUpTo {Q : ℕ} {p : Σ k : ℕ, DirichletCharacter ℂ (k + 1)} :
    p ∈ primCharsUpTo Q ↔ p.1 + 1 ≤ Q ∧ p.2.IsPrimitive := by
  classical
  simp only [primCharsUpTo, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact and_congr_left' (by omega)

open Classical in
theorem sum_primCharsUpTo (Q : ℕ) (f : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ) :
    ∑ p ∈ primCharsUpTo Q, f p =
      ∑ k ∈ Finset.range Q,
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          f ⟨k, χ⟩ :=
  Finset.sum_sigma _ _ _

/-- **Large-Sieve Mean-Square Bound over `primCharsUpTo Q`** (`Finset.Icc M₁ M₂`). -/
theorem primCharsUpTo_mean_square_le (Q M₁ M₂ : ℕ) (c : ℕ → ℂ) :
    ∑ p ∈ primCharsUpTo Q, ‖∑ n ∈ Finset.Icc M₁ M₂, c n * p.2 (n : ZMod (p.1 + 1))‖ ^ 2 ≤
      (((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2 := by
  rw [sum_primCharsUpTo]
  exact multiplicative_large_sieve_Icc_range Q M₁ M₂ c

/-- **Multi-Modulus Bad Primitive Character Count (via `ZeroDensityWindow.chebyshev_bad_card`)**:
any set `B` of primitive characters of conductor `≤ Q` where `‖∑_{n ∈ Icc M₁ M₂} c n * χ(n)‖ ≥ V`
has cardinality at most `((M₂ + 1 - M₁ + 3 Q²) / V²) * ∑ |c n|²`. -/
theorem large_sieve_bad_primitive_chars_card_le (Q M₁ M₂ : ℕ) (c : ℕ → ℂ)
    (B : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))) {V : ℝ} (hV : 0 < V)
    (hB_sub : ∀ p ∈ B, p.1 + 1 ≤ Q ∧ p.2.IsPrimitive)
    (hBad : ∀ p ∈ B, V ≤ ‖∑ n ∈ Finset.Icc M₁ M₂, c n * p.2 (n : ZMod (p.1 + 1))‖) :
    (B.card : ℝ) ≤
      ((((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) *
        ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2 := by
  classical
  have hsub : B ⊆ primCharsUpTo Q := fun p hp => mem_primCharsUpTo.mpr (hB_sub p hp)
  rcases Nat.eq_zero_or_pos (primCharsUpTo Q).card with h0 | hpos
  · have hB0 : B.card = 0 := Nat.eq_zero_of_le_zero ((Finset.card_le_card hsub).trans_eq h0)
    rw [hB0, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hPpos : (0 : ℝ) < ((primCharsUpTo Q).card : ℝ) := Nat.cast_pos.mpr hpos
    set M : ℝ := ((((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) *
      ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2) / ((primCharsUpTo Q).card : ℝ)
    have hcheb := ZeroDensityWindow.chebyshev_bad_card hsub
      (fun p => ‖∑ n ∈ Finset.Icc M₁ M₂, c n * p.2 (n : ZMod (p.1 + 1))‖) hV
      (by
        rw [show M * ((primCharsUpTo Q).card : ℝ) =
          (((M₂ + 1 - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc M₁ M₂, ‖c n‖ ^ 2 by
          dsimp only [M]; rw [div_mul_cancel₀ _ hPpos.ne']]
        exact primCharsUpTo_mean_square_le Q M₁ M₂ c)
      (fun p hp => by rw [abs_of_nonneg (norm_nonneg _)]; exact hBad p hp)
    refine hcheb.trans_eq ?_
    dsimp only [M]
    field_simp [hPpos.ne', hV.ne']

/-- **Multi-Modulus Good Primitive Character Share (via `ZeroDensityWindow.share_of_bad`)**:
extracts a large subset `G ⊆ primCharsUpTo Q` on which `‖∑_{n=1}^N c n * χ(n)‖ < V`. -/
theorem large_sieve_good_primitive_chars_share (Q N : ℕ) (c : ℕ → ℂ) {V : ℝ} (hV : 0 < V) :
    ∃ G ⊆ primCharsUpTo Q,
      ((primCharsUpTo Q).card : ℝ) -
        (((N : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 ≤ (G.card : ℝ) ∧
      ∀ p ∈ G, ‖∑ n ∈ Finset.Icc 1 N, c n * p.2 (n : ZMod (p.1 + 1))‖ < V := by
  classical
  rcases Nat.eq_zero_or_pos (primCharsUpTo Q).card with h0 | hpos
  · refine ⟨∅, Finset.empty_subset _, ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
    rw [h0, Finset.card_empty, Nat.cast_zero, zero_sub]
    have hnn : 0 ≤ (((N : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  · have hPpos : (0 : ℝ) < ((primCharsUpTo Q).card : ℝ) := Nat.cast_pos.mpr hpos
    set η : ℝ := ((((N : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) *
      ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2) / ((primCharsUpTo Q).card : ℝ)
    obtain ⟨G, hGs, hGc, hG⟩ := ZeroDensityWindow.share_of_bad (primCharsUpTo Q) (η := η)
      (fun p => ‖∑ n ∈ Finset.Icc 1 N, c n * p.2 (n : ZMod (p.1 + 1))‖ < V)
      (fun B hBs hB => by
        rw [show η * ((primCharsUpTo Q).card : ℝ) =
            (((N : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 by
          dsimp only [η]; rw [div_mul_cancel₀ _ hPpos.ne']]
        have hN : (N + 1 - 1 : ℕ) = N := by omega
        simpa only [hN] using large_sieve_bad_primitive_chars_card_le Q 1 N c B hV
          (fun p hp => mem_primCharsUpTo.mp (hBs hp))
          (fun p hp => not_lt.mp (hB p hp)))
    refine ⟨G, hGs, ?_, hG⟩
    rw [show ((primCharsUpTo Q).card : ℝ) -
        (((N : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 =
        (1 - η) * ((primCharsUpTo Q).card : ℝ) by
      dsimp only [η]; rw [sub_mul, one_mul, div_mul_cancel₀ _ hPpos.ne']]
    exact hGc

/-- **Explicit Power-Saving Large-Values Bound for Dyadic Dirichlet Polynomials** (`Q^(1/100) ≤ Q^(1/4)`):
at the zero-free-box abscissa `σ = 1 - 1/400` and dyadic scale `M = Q²`, any set `B` of primitive
characters of conductor `≤ Q` (`Q ≥ 1`) with `V ≤ ‖∑_{n ∈ Icc M (2*M)} a n * χ(n) * n^(-s)‖`
(where `1 - 1/400 ≤ s.re` and `‖a n‖ ≤ B₀`) satisfies the power-saving count
`|B| ≤ (10 * B₀² / V²) * Q^(1/100) ≤ (10 * B₀² / V²) * Q^(1/4)`. -/
theorem dyadic_dirichlet_poly_large_values_power_saving {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℂ) {B₀ V : ℝ} (hB₀ : 0 ≤ B₀) (hV : 0 < V)
    (ha : ∀ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2), ‖a n‖ ≤ B₀)
    {s : ℂ} (hs : 1 - (1 : ℝ) / 400 ≤ s.re)
    (B : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)))
    (hB_sub : ∀ p ∈ B, p.1 + 1 ≤ Q ∧ p.2.IsPrimitive)
    (hBad : ∀ p ∈ B, V ≤ ‖∑ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2),
      a n * p.2 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-s)‖) :
    (B.card : ℝ) ≤ (10 * B₀ ^ 2 / V ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 100) ∧
    (10 * B₀ ^ 2 / V ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 100) ≤
      (10 * B₀ ^ 2 / V ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 4) := by
  let c : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-s)
  have hBad' : ∀ p ∈ B, V ≤ ‖∑ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2), c n * p.2 (n : ZMod (p.1 + 1))‖ := by
    intro p hp
    refine (hBad p hp).trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [c]; ring
  have hLS := large_sieve_bad_primitive_chars_card_le Q (Q ^ 2) (2 * Q ^ 2) c B hV hB_sub hBad'
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hlen : (((2 * Q ^ 2 + 1 - Q ^ 2 : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) ≤ 5 * (Q : ℝ) ^ 2 := by
    have hnat : 2 * Q ^ 2 + 1 - Q ^ 2 = Q ^ 2 + 1 := by omega
    rw [hnat]; push_cast
    have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ hQ1
    linarith
  have hl2 : ∑ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2), ‖c n‖ ^ 2 ≤
      2 * B₀ ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100)) := by
    have hterm : ∀ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2),
        ‖c n‖ ^ 2 ≤ B₀ ^ 2 * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400))) := by
      intro n hn
      have hn_ge : Q ^ 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by
        have : 1 ≤ n := le_trans (by nlinarith) hn_ge
        exact_mod_cast (by omega : 0 < n)
      have hn_geR : (Q : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn_ge
      have hns : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos (Nat.cast_pos.mp hn_pos)]
        simp
      have hre_le : (n : ℝ) ^ (-s.re) ≤ ((Q : ℝ) ^ 2) ^ (-(1 - (1 : ℝ) / 400)) := by
        calc (n : ℝ) ^ (-s.re)
            ≤ (n : ℝ) ^ (-(1 - (1 : ℝ) / 400)) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (le_trans (by nlinarith : 1 ≤ Q ^ 2) hn_ge)) (by linarith)
          _ ≤ ((Q : ℝ) ^ 2) ^ (-(1 - (1 : ℝ) / 400)) :=
              Real.rpow_le_rpow_of_nonpos (pow_pos hQpos 2) hn_geR (by norm_num)
      have hcn : ‖c n‖ ≤ B₀ * ((Q : ℝ) ^ 2) ^ (-(1 - (1 : ℝ) / 400)) := by
        dsimp only [c]
        rw [norm_mul, hns]
        exact mul_le_mul (ha n hn) hre_le (Real.rpow_nonneg hn_pos.le _) hB₀
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hcn 2
      refine hsq.trans_eq ?_
      rw [mul_pow, ← Real.rpow_natCast (((Q : ℝ) ^ 2) ^ _), ← Real.rpow_mul (pow_nonneg hQpos.le 2)]
      congr 2; push_cast; ring
    have hcard : ((Finset.Icc (Q ^ 2) (2 * Q ^ 2)).card : ℝ) ≤ 2 * (Q : ℝ) ^ 2 := by
      rw [Nat.card_Icc]
      have hnat : 2 * Q ^ 2 + 1 - Q ^ 2 = Q ^ 2 + 1 := by omega
      rw [hnat]; push_cast
      have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ hQ1
      linarith
    calc ∑ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2), ‖c n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2),
            B₀ ^ 2 * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400))) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc (Q ^ 2) (2 * Q ^ 2)).card : ℝ) *
            (B₀ ^ 2 * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (Q : ℝ) ^ 2) * (B₀ ^ 2 * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400)))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * B₀ ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100)) := by
          have hpow : ((Q : ℝ) ^ 2) * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400))) =
              (Q : ℝ) ^ (-((199 : ℝ) / 100)) := by
            have hq2 : (Q : ℝ) ^ 2 = (Q : ℝ) ^ (2 : ℝ) := (Real.rpow_two (Q : ℝ)).symm
            rw [hq2, ← Real.rpow_mul hQpos.le, ← Real.rpow_add hQpos]
            congr 1; norm_num
          calc (2 * (Q : ℝ) ^ 2) * (B₀ ^ 2 * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400))))
              = 2 * B₀ ^ 2 * (((Q : ℝ) ^ 2) * ((Q : ℝ) ^ 2) ^ (-(2 * (1 - (1 : ℝ) / 400)))) := by ring
            _ = 2 * B₀ ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100)) := by rw [hpow]
  have h1 : (B.card : ℝ) ≤ (10 * B₀ ^ 2 / V ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 100) := by
    refine hLS.trans ?_
    have hmul :
        ((((2 * Q ^ 2 + 1 - Q ^ 2 : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) / V ^ 2) *
          ∑ n ∈ Finset.Icc (Q ^ 2) (2 * Q ^ 2), ‖c n‖ ^ 2 ≤
        (5 * (Q : ℝ) ^ 2 / V ^ 2) * (2 * B₀ ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100))) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hlen (sq_nonneg V)) hl2
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    refine hmul.trans_eq ?_
    have hpow : (Q : ℝ) ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100)) = (Q : ℝ) ^ ((1 : ℝ) / 100) := by
      rw [← Real.rpow_two (Q : ℝ), ← Real.rpow_add hQpos]
      congr 1; norm_num
    calc (5 * (Q : ℝ) ^ 2 / V ^ 2) * (2 * B₀ ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100)))
        = (10 * B₀ ^ 2 / V ^ 2) * ((Q : ℝ) ^ 2 * (Q : ℝ) ^ (-((199 : ℝ) / 100))) := by ring
      _ = (10 * B₀ ^ 2 / V ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 100) := by rw [hpow]
  refine ⟨h1, ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by positivity)

/-- **Large-Sieve Zero Detector Hypothesis** for `ZeroDensityWindow.ZeroDensityBoxBound C`:
for every `Q ≥ 3`, zeros in the box `Re(s) > 1 - 1/400, |Im(s)| ≤ Q` are detected by a finite
net `G` of Dirichlet polynomials `(M₁, M₂, c_g, V_g)` whose aggregate large-sieve energy is
`≤ C * Q^(1/4)`. -/
def HasLargeSieveZeroDetector (C : ℝ) : Prop :=
  ∀ Q : ℝ, 3 ≤ Q →
    ∃ (ι : Type) (_ : Fintype ι) (M₁ M₂ : ι → ℕ) (c : ι → ℕ → ℂ) (V : ι → ℝ),
      (∀ i, 0 < V i) ∧
      (∑ i : ι, ((((M₂ i + 1 - M₁ i : ℕ) : ℝ) + 3 * (⌊Q⌋₊ : ℝ) ^ 2) / (V i) ^ 2) *
          ∑ n ∈ Finset.Icc (M₁ i) (M₂ i), ‖c i n‖ ^ 2 ≤ C * Q ^ ((1 : ℝ) / 4)) ∧
      ∀ (p : Σ k : ℕ, DirichletCharacter ℂ (k + 1)),
        p.2.IsPrimitive → ((p.1 + 1 : ℕ) : ℝ) ≤ Q →
        (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
        ∃ i : ι, V i ≤ ‖∑ n ∈ Finset.Icc (M₁ i) (M₂ i), c i n * p.2 (n : ZMod (p.1 + 1))‖

/-- **Direct Bridge into `ZeroDensityWindow.ZeroDensityBoxBound`**:
any Large-Sieve zero detector of energy `≤ C * Q^(1/4)` unconditionally implies
`ZeroDensityWindow.ZeroDensityBoxBound C` via our Multiplicative Large Sieve! -/
theorem zeroDensityBoxBound_of_largeSieveDetector {C : ℝ}
    (hDet : HasLargeSieveZeroDetector C) :
    ZeroDensityWindow.ZeroDensityBoxBound C := by
  classical
  intro Q F hQ hF
  obtain ⟨ι, hfin, M₁, M₂, c, V, hV, hEnergy, hDetect⟩ := hDet Q hQ
  have hcover : F ⊆ Finset.univ.biUnion (fun i : ι =>
      F.filter fun p => V i ≤ ‖∑ n ∈ Finset.Icc (M₁ i) (M₂ i), c i n * p.2 (n : ZMod (p.1 + 1))‖) := by
    intro p hp
    obtain ⟨hprim, hle, hzero⟩ := hF p hp
    obtain ⟨i, hi⟩ := hDetect p hprim hle hzero
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hp, hi⟩⟩
  have hcard_le : (F.card : ℝ) ≤
      ∑ i : ι, ((F.filter fun p =>
        V i ≤ ‖∑ n ∈ Finset.Icc (M₁ i) (M₂ i), c i n * p.2 (n : ZMod (p.1 + 1))‖).card : ℝ) := by
    have hnat : F.card ≤ ∑ i : ι, (F.filter fun p =>
        V i ≤ ‖∑ n ∈ Finset.Icc (M₁ i) (M₂ i), c i n * p.2 (n : ZMod (p.1 + 1))‖).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  refine hcard_le.trans ((Finset.sum_le_sum fun i _ => ?_).trans hEnergy)
  refine large_sieve_bad_primitive_chars_card_le ⌊Q⌋₊ (M₁ i) (M₂ i) (c i) _ (hV i) ?_ ?_
  · intro p hp
    have hpf := (Finset.mem_filter.mp hp).1
    obtain ⟨hprim, hle, _⟩ := hF p hpf
    exact ⟨Nat.le_floor hle, hprim⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2

/-- **End-to-End Bad-Prime Counting Corollary** (`ZeroDensityWindow.count_bad_of_zeroDensityBox`):
a Large-Sieve zero detector directly implies `|S| ≤ max C 0 * Q^(1/4)` for bad primes `q > F`. -/
theorem count_bad_primes_of_largeSieveDetector {C : ℝ}
    (hDet : HasLargeSieveZeroDetector C)
    (Q F : ℝ) (S : Finset ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ q ∈ S, q.Prime ∧ F < (q : ℝ) ∧
      ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧
          ¬ ZeroDensityWindow.ZeroFreeBox Q ψ) :
    (S.card : ℝ) ≤ max C 0 * Q ^ (1 / 4 : ℝ) :=
  ZeroDensityWindow.count_bad_of_zeroDensityBox
    (zeroDensityBoxBound_of_largeSieveDetector hDet) Q F S hQ hS

/-! ### Bridges to `Stage2DirichletAP` (Unconditional Large-Sieve Chebyshev & AP Variance Bounds) -/

/-- Exact identification of `Stage2DirichletAP.chebyshevPsiChar` with a sum over `Finset.Icc 1 ⌊x⌋₊`. -/
theorem chebyshevPsiChar_eq_sum_Icc {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ (n : ZMod q) := by
  unfold Stage2DirichletAP.chebyshevPsiChar
  have hsplit : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : 0 ∉ Finset.Icc 1 ⌊x⌋₊ := by simp
  rw [hsplit, Finset.sum_insert h0, ArithmeticFunction.map_zero,
    Complex.ofReal_zero, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- Elementary `L²` von Mangoldt energy bound: `∑_{n=1}^{⌊x⌋} Λ(n)² ≤ (log x) * ψ(x)` for `x ≥ 1`. -/
theorem sum_vonMangoldt_sq_le_log_mul_psi {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2 ≤ Real.log x * chebyshevPsi x := by
  have hpsi : chebyshevPsi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
    unfold chebyshevPsi
    have hsplit : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  rw [hpsi, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have hn_le : (n : ℝ) ≤ x :=
    (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
  have hnorm : ‖(Λ n : ℂ)‖ = Λ n := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hnorm, sq]
  have hlog : Λ n ≤ Real.log x :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn_pos hn_le)
  exact mul_le_mul_of_nonneg_right hlog ArithmeticFunction.vonMangoldt_nonneg

open Classical in
/-- **Unconditional Bombieri–Vinogradov / Large-Sieve Mean-Square Bound for `Stage2DirichletAP.chebyshevPsiChar`**:
averaged over all primitive characters `χ mod q` with `1 ≤ q ≤ Q` and `x ≥ 1`,
`∑_{q ≤ Q} (q / φ(q)) ∑*_{χ mod q} ‖ψ(x, χ)‖² ≤ (x + 3 Q²) * (log x) * ψ(x)`. -/
theorem prim_chebyshevPsiChar_mean_square_le (Q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
      (x + 3 * (Q : ℝ) ^ 2) * (Real.log x * chebyshevPsi x) := by
  have hLS := multiplicative_large_sieve_Icc Q ⌊x⌋₊ (fun n => (Λ n : ℂ))
  have hrewrite :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 =
        ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ (n : ZMod (k + 1))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [chebyshevPsiChar_eq_sum_Icc]
  rw [hrewrite]
  refine hLS.trans ?_
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  exact mul_le_mul (by linarith) (sum_vonMangoldt_sq_le_log_mul_psi hx)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- **Unconditional Bad Primitive Character Count for `Stage2DirichletAP.chebyshevPsiChar`**:
at most `((x + 3 Q²) / V²) * (log x * ψ(x))` primitive characters of conductor `≤ Q` can have
`‖ψ(x, χ)‖ ≥ V`. -/
theorem bad_chebyshevPsiChar_card_le (Q : ℕ) {x V : ℝ} (hx : 1 ≤ x) (hV : 0 < V)
    (B : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)))
    (hB_sub : ∀ p ∈ B, p.1 + 1 ≤ Q ∧ p.2.IsPrimitive)
    (hBad : ∀ p ∈ B, V ≤ ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖) :
    (B.card : ℝ) ≤ ((x + 3 * (Q : ℝ) ^ 2) / V ^ 2) * (Real.log x * chebyshevPsi x) := by
  have hBad' : ∀ p ∈ B, V ≤ ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * p.2 (n : ZMod (p.1 + 1))‖ :=
    fun p hp => (hBad p hp).trans_eq (by rw [chebyshevPsiChar_eq_sum_Icc])
  have hLS := large_sieve_bad_primitive_chars_card_le Q 1 ⌊x⌋₊ (fun n => (Λ n : ℂ)) B hV hB_sub hBad'
  have hlen : (⌊x⌋₊ + 1 - 1 : ℕ) = ⌊x⌋₊ := by omega
  rw [hlen] at hLS
  refine hLS.trans ?_
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  exact mul_le_mul (div_le_div_of_nonneg_right (by linarith) (sq_nonneg V))
    (sum_vonMangoldt_sq_le_log_mul_psi hx)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

open Classical in
/-- **Exact Barban–Davenport–Halberstam / Plancherel AP Variance Identity** for
`Stage2DirichletAP.chebyshevPsiAP`:
`∑_{a ∈ (ZMod q)ˣ} (ψ(x; q, a.val) - ψ_coprime(x; q) / φ(q))² = φ(q)⁻¹ ∑_{χ ≠ 1} ‖ψ(x, χ)‖²`. -/
theorem psiAP_variance_eq_nonprincipal_chars {q : ℕ} [NeZero q] (x : ℝ) :
    ∑ a : (ZMod q)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
          Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) ^ 2 =
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 := by
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hparseval := Stage2BehrendSieve.dirichlet_parseval_residue_classes (q := q)
    (Finset.Icc 1 ⌊x⌋₊) (fun n => (Λ n : ℂ))
  have hL : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ (n : ZMod q)‖ ^ 2 =
      Stage2DirichletAP.chebyshevPsiCoprime q x ^ 2 +
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 := by
    simp_rw [← chebyshevPsiChar_eq_sum_Icc]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
    congr 1
    rw [Stage2DirichletAP.chebyshevPsiChar_one_eq_coprime, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hR_term : ∀ a : (ZMod q)ˣ,
      ‖∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q)), (Λ n : ℂ)‖ ^ 2 =
        Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x ^ 2 := by
    intro a
    have hsum_eq :
        ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q)), (Λ n : ℂ) =
          (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x : ℂ) := by
      unfold Stage2DirichletAP.chebyshevPsiAP
      rw [Complex.ofReal_sum, Finset.sum_filter]
      have hsplit : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have h0 : ((if 0 ≡ (a : ZMod q).val [MOD q] then Λ 0 else 0 : ℝ) : ℂ) = 0 := by
        simp [ArithmeticFunction.map_zero]
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hiff : (n : ZMod q) = (a : ZMod q) ↔ n ≡ (a : ZMod q).val [MOD q] := by
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
      by_cases h : (n : ZMod q) = (a : ZMod q)
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hm => h (hiff.mpr hm)), Complex.ofReal_zero]
    rw [hsum_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hR_term] at hparseval
  rw [hL] at hparseval
  -- Also prove `∑_{a : (ZMod q)ˣ} ψ(x; q, a.val) = ψ_coprime(x; q)` to expand the variance square!
  have hsum_ap : ∑ a : (ZMod q)ˣ, Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x =
      Stage2DirichletAP.chebyshevPsiCoprime q x := by
    unfold Stage2DirichletAP.chebyshevPsiAP Stage2DirichletAP.chebyshevPsiCoprime
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop]
      obtain ⟨a₀, ha₀⟩ := (ZMod.isUnit_iff_coprime n q).mpr hcop
      rw [Finset.sum_eq_single a₀]
      · have hmod : n ≡ (a₀ : ZMod q).val [MOD q] := by
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ha₀]
        rw [if_pos hmod]
      · intro a _ hne
        have hnot : ¬ n ≡ (a : ZMod q).val [MOD q] := by
          intro hmod
          rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
          exact hne (Units.ext (hmod.symm.trans ha₀.symm))
        rw [if_neg hnot]
      · intro h; exact absurd (Finset.mem_univ a₀) h
    · rw [if_neg hcop]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hnot : ¬ n ≡ (a : ZMod q).val [MOD q] := by
        intro hmod
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
        exact hcop ((ZMod.isUnit_iff_coprime n q).mp (hmod ▸ a.isUnit))
      rw [if_neg hnot]
  have hexpand :
      ∑ a : (ZMod q)ˣ,
          (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
            Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) ^ 2 =
        (∑ a : (ZMod q)ˣ, Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x ^ 2) -
          Stage2DirichletAP.chebyshevPsiCoprime q x ^ 2 / (Nat.totient q : ℝ) := by
    have h1 : ∀ a : (ZMod q)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
          Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) ^ 2 =
        Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x ^ 2 -
          2 * (Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) *
            Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x +
          (Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) ^ 2 := fun _ => by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_ap,
      Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
    field_simp [hphi_pos.ne']
    ring
  rw [hexpand]
  have hdiv :
      ∑ a : (ZMod q)ˣ, Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x ^ 2 =
        (Stage2DirichletAP.chebyshevPsiCoprime q x ^ 2 +
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) / (Nat.totient q : ℝ) := by
    rw [eq_div_iff hphi_pos.ne', mul_comm]
    exact hparseval.symm
  rw [hdiv]
  field_simp [hphi_pos.ne']
  ring

/-- **Unconditional Single-Modulus AP Variance Bound** for `Stage2DirichletAP.chebyshevPsiAP`:
`∑_{a ∈ (ZMod q)ˣ} (ψ(x; q, a.val) - ψ_coprime(x; q) / φ(q))² ≤ (1 + x / φ(q)) * log x * ψ(x)`. -/
theorem psiAP_variance_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    ∑ a : (ZMod q)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
          Stage2DirichletAP.chebyshevPsiCoprime q x / (Nat.totient q : ℝ)) ^ 2 ≤
      (1 + x / (Nat.totient q : ℝ)) * (Real.log x * chebyshevPsi x) := by
  classical
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [psiAP_variance_eq_nonprincipal_chars]
  have hsub :
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
        ∑ χ : DirichletCharacter ℂ q,
          ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ (n : ZMod q)‖ ^ 2 := by
    simp_rw [← chebyshevPsiChar_eq_sum_Icc]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => sq_nonneg _
  have hms := Stage2BehrendSieve.dirichlet_mean_square_Icc (q := q) ⌊x⌋₊ (fun n => (Λ n : ℂ))
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  calc (Nat.totient q : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
      ≤ (Nat.totient q : ℝ)⁻¹ *
          (((Nat.totient q : ℝ) + (⌊x⌋₊ : ℝ)) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hsub.trans (hms.1.le.trans hms.2)) (inv_nonneg.mpr hphi_pos.le)
    _ ≤ (Nat.totient q : ℝ)⁻¹ *
          (((Nat.totient q : ℝ) + x) * (Real.log x * chebyshevPsi x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
        exact mul_le_mul (by linarith) (sum_vonMangoldt_sq_le_log_mul_psi hx)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = (1 + x / (Nat.totient q : ℝ)) * (Real.log x * chebyshevPsi x) := by
        field_simp [hphi_pos.ne']

end Stage3BombieriVinogradov
end RHDirect

end
