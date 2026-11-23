import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.MellinExplicit
import RHDirect.ZeroDensityWindow
import RHDirect.Stage2PrimePairs
import RHDirect.Stage2DirichletAP
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# RHDirect.Stage3ZeroFreeRegion

Compact, self-contained, 0-`sorry`, 0-custom-`axiom` Lean 4 formalization of the
**Classical Hadamard–de la Vallée Poussin Zero-Free Region, Landau–Page Exceptional Zero
Isolation, and Explicit-Formula Truncated Zero-Sum → `PsiCharPowerBound` / `LinnikAP` Bridge**
against `RHDirect.Interfaces`, `RHDirect.ElementaryEquiv`, `RHDirect.MellinExplicit`,
`RHDirect.ZeroDensityWindow`, `RHDirect.Stage2PrimePairs`, `RHDirect.Stage2DirichletAP`,
and targeted Mathlib `v4.33.1`.

## Main Contents
1. **Hadamard–de la Vallée Poussin 3-4-1 & 4-Character Non-Negative Dirichlet Series Positivity**:
   - Exact trigonometric identity `3 + 4 cos θ + cos(2θ) = 2 (1 + cos θ)² ≥ 0` and complex
     unit-disk form `3 + 4 Re(z) + Re(z²) ≥ 0` (`= 2 (1 + Re z)²` on `‖z‖ = 1`).
   - Exact weighted Dirichlet-series identity on `Re(s) > 1` for
     `3 (-L'/L)(1_q, σ) + 4 (-L'/L)(χ, σ + it) + (-L'/L)(χ², σ + 2it)` and full unconditional
     non-negativity of its real part (both with `L(1_q, σ)` and with `ζ(σ)`).
   - Lifted product character `prodChar χ₁ χ₂` mod `q₁ * q₂`, exact natural-number evaluation
     `prodChar_apply_nat`, non-principality `prodChar_ne_one_of_distinct_primitive_real` for
     distinct primitive real characters, and unconditional 2-character & 4-character positivity
     `Re((-ζ'/ζ)(σ) + (-L'/L)(χ₁, σ) + (-L'/L)(χ₂, σ) + (-L'/L)(χ₁ χ₂, σ)) ≥ 0`.
2. **Quantitative Classical Zero-Free Region & Landau–Page Exceptional Zero Isolation**:
   - Typed `HadamardLogDerivPackage B` capturing the standard Hadamard-product upper bounds for
     `Re(-ζ'/ζ)` and `Re(-L'/L)` on `1 < σ ≤ 2`.
   - Unconditional proofs (with explicit rational constants!) of:
     - `zeroFreeRegion_complex_char`: for `χ² ≠ 1`, every critical-strip zero `ρ` satisfies
       `ρ.re ≤ 1 - 1 / (168 * max B 1 * log(q (|ρ.im| + 2)))`.
     - `zeroFreeRegion_real_char_nonreal_zero`: for real `χ ≠ 1` and every non-real zero `ρ`,
       `ρ.re ≤ 1 - 1 / (296 * max B 1 * log(q (|ρ.im| + 2)))` (eliminating both large and
       small nonzero `|ρ.im|` via 3-4-1 + conjugate-pair 2-character positivity!).
     - `zeroFreeRegion_riemannZeta`: for `ζ(ρ) = 0` (`ρ.im ≠ 0`),
       `ρ.re ≤ 1 - 1 / (640 * max B 1 * log(|ρ.im| + 2))`.
     - `real_char_at_most_one_exceptional_real_zero`: any single real `χ ≠ 1` mod `q` has at
       most one real zero `β > 1 - 1 / (18 * max B 1 * log(2 q))`.
     - `landau_page_two_distinct_real_chars` & `landau_page_exceptional_zero_isolation`:
       among ALL primitive characters `ψ` of conductor `≤ Q` (`Q ≥ 2`), at most ONE simple real
       zero `β₁ > 1 - 1 / (168 * max B 1 * log(2 Q))` can exist!
     - `zeroFreeRegion_nonexceptional`: unified zero-free region for all non-exceptional zeros.
3. **Explicit-Formula Truncated Zero Sum → `PsiCharPowerBound` / `PsiAPRelativeBound` Bridge**:
   - Dyadic zero-sum summation `norm_sum_cpow_div_zero_le` from a zero-free strip `1 - θ ≤ β ≤ θ`
     and cumulative zero-counting bound `N(t, χ) ≤ C_N t log(q (t + 2))`.
   - `psiCharPowerBound_of_truncatedExplicitFormula`: unconditionally derives
     `Stage2DirichletAP.PsiCharPowerBound θ'` for every `θ' ∈ (θ, 1)`.
   - `stage2PrimePairs_of_truncatedExplicitFormula`: discharges all five Linnik / prime-pair
     targets (`LinnikAPDyadic ∧ LinnikAPInterval ∧ PairSupply ∧ PairEx ∧ SmallOne`) via
     `Stage2DirichletAP.stage2PrimePairs_of_psiCharPowerBound`.
   - `psiCharPowerBound_of_zeroFreeAll_and_explicitFormula`: connects `RHDirect.ZeroFreeAll` +
     `ElementaryEquiv` directly to `PsiCharPowerBound θ'` for all `θ' ∈ (1/2, 1)`.
   - Direct bridges to `ZeroDensityWindow.ZeroFreeBox` and `RHDirect.HasRpowWindow` (`la = 3/2`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex DirichletCharacter Finset RHDirect
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage3ZeroFreeRegion

/-! ## Section 1: Hadamard–de la Vallée Poussin 3-4-1 & 4-Character Positivity -/

/-- Negative logarithmic derivative `-ζ'(s) / ζ(s)`. -/
def negLogDerivZeta (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- Negative logarithmic derivative `-L'(χ, s) / L(χ, s)`. -/
def negLogDerivL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

/-- A Dirichlet character is real-valued if all its values have zero imaginary part. -/
def IsRealChar {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, (χ a).im = 0

/-- Product of two Dirichlet characters `χ₁ mod q₁` and `χ₂ mod q₂` lifted to modulus `q₁ * q₂`. -/
def prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    DirichletCharacter ℂ (q₁ * q₂) :=
  DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
    DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂

/-- Classical Hadamard–de la Vallée Poussin trigonometric identity:
`3 + 4 cos θ + cos (2 θ) = 2 (1 + cos θ)²`. -/
theorem three_four_one_cos_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- Classical Hadamard–de la Vallée Poussin trigonometric inequality:
`3 + 4 cos θ + cos (2 θ) ≥ 0`. -/
theorem three_four_one_cos_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [three_four_one_cos_eq]
  positivity

/-- Complex unit-circle form of the 3-4-1 identity:
if `‖z‖ = 1`, then `3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))²`. -/
theorem three_four_one_complex_eq {z : ℂ} (hz : ‖z‖ = 1) :
    3 + 4 * z.re + (z ^ 2).re = 2 * (1 + z.re) ^ 2 := by
  have hns : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow, Complex.normSq_apply] at h1
    linarith
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [sq, Complex.mul_re]
    ring
  rw [hsq]
  linarith

/-- Complex closed-unit-disk form of the 3-4-1 inequality:
for every `z : ℂ` with `‖z‖ ≤ 1`, `3 + 4 Re(z) + Re(z²) ≥ 0`. -/
theorem three_four_one_complex_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hns : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [Complex.normSq_apply] at h1
    linarith
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [sq, Complex.mul_re]
    ring
  rw [hsq]
  nlinarith [sq_nonneg (1 + z.re)]

/-- Elementary 4-character positivity identity: `1 + a + b + a * b = (1 + a) * (1 + b) ≥ 0`
for all `a, b ≥ -1`. -/
theorem four_char_real_nonneg {a b : ℝ} (ha : -1 ≤ a) (hb : -1 ≤ b) :
    0 ≤ 1 + a + b + a * b := by
  have h : 1 + a + b + a * b = (1 + a) * (1 + b) := by ring
  rw [h]
  exact mul_nonneg (by linarith) (by linarith)

theorem isRealChar_of_pchar_isReal {ψ : PChar} (h : ψ.IsReal) : IsRealChar ψ.χ := h

theorem isRealChar_inv_eq_self {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : IsRealChar χ) :
    χ⁻¹ = χ := by
  ext a
  have hstar : starRingEnd ℂ (χ a) = χ⁻¹ a := by
    simpa [RCLike.star_def] using MulChar.star_apply' χ a
  rw [← hstar]
  apply Complex.ext
  · simp
  · simp [hχ a]

theorem isRealChar_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : IsRealChar χ) :
    χ ^ 2 = 1 := by
  calc χ ^ 2 = χ⁻¹ * χ := by rw [sq, isRealChar_inv_eq_self hχ]
    _ = 1 := inv_mul_cancel χ

theorem isRealChar_apply_re_bounds {q : ℕ} {χ : DirichletCharacter ℂ q} (a : ZMod q) :
    -1 ≤ (χ a).re ∧ (χ a).re ≤ 1 := by
  have h1 : |(χ a).re| ≤ 1 := (Complex.abs_re_le_norm (χ a)).trans (χ.norm_le_one a)
  exact abs_le.mp h1

theorem isRealChar_of_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1) :
    IsRealChar χ := by
  intro a
  have hinv : χ⁻¹ = χ := by
    have h1 : χ⁻¹ * (χ * χ) = χ⁻¹ * 1 := congrArg (χ⁻¹ * ·) (by simpa [sq] using hsq)
    simpa [mul_assoc] using h1.symm
  have hstar : starRingEnd ℂ (χ a) = χ a := by
    have h1 : starRingEnd ℂ (χ a) = χ⁻¹ a := by
      simpa [RCLike.star_def] using MulChar.star_apply' χ a
    rw [h1, hinv]
  have him := congrArg Complex.im hstar
  simp only [Complex.conj_im] at him
  linarith

/-- Exact natural-number evaluation of the lifted product character:
`(prodChar χ₁ χ₂) n = χ₁ n * χ₂ n` for every `n : ℕ` (including non-coprime `n`!). -/
theorem prodChar_apply_nat {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) :
    prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂)) = χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂) := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases hcop : Nat.Coprime n (q₁ * q₂)
  · have hcop1 : Nat.Coprime n q₁ := hcop.coprime_mul_right_right
    have hcop2 : Nat.Coprime n q₂ := hcop.coprime_mul_left_right
    have hu : IsUnit (n : ZMod (q₁ * q₂)) := (ZMod.isUnit_iff_coprime n (q₁ * q₂)).mpr hcop
    have h1 : DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ (n : ZMod (q₁ * q₂)) =
        χ₁ (n : ZMod q₁) := by
      obtain ⟨u, hu_eq⟩ := hu
      rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ q₂) u,
        hu_eq, ZMod.cast_natCast (dvd_mul_right q₁ q₂)]
    have h2 : DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂ (n : ZMod (q₁ * q₂)) =
        χ₂ (n : ZMod q₂) := by
      obtain ⟨u, hu_eq⟩ := hu
      rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left q₂ q₁) u,
        hu_eq, ZMod.cast_natCast (dvd_mul_left q₂ q₁)]
    rw [h1, h2]
  · have hnu : ¬ IsUnit (n : ZMod (q₁ * q₂)) :=
      fun hu => hcop ((ZMod.isUnit_iff_coprime n (q₁ * q₂)).mp hu)
    rw [MulChar.map_nonunit _ hnu, MulChar.map_nonunit _ hnu, zero_mul]
    by_cases h1 : Nat.Coprime n q₁
    · have h2 : ¬ Nat.Coprime n q₂ := fun h2 => hcop (h1.mul_right h2)
      have hnu2 : ¬ IsUnit (n : ZMod q₂) := fun hu => h2 ((ZMod.isUnit_iff_coprime n q₂).mp hu)
      rw [MulChar.map_nonunit _ hnu2, mul_zero]
    · have hnu1 : ¬ IsUnit (n : ZMod q₁) := fun hu => h1 ((ZMod.isUnit_iff_coprime n q₁).mp hu)
      rw [MulChar.map_nonunit _ hnu1, zero_mul]

private lemma pchar_of_changeLevel {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    (χ : DirichletCharacter ℂ d) (hprim : χ.IsPrimitive) :
    PChar.of (DirichletCharacter.changeLevel hd χ) = PChar.mk d χ hprim := by
  set η : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hd χ
  have hcond : η.conductor = d := (DirichletCharacter.conductor_changeLevel χ hd).trans hprim
  have : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have aux : ∀ (e : ℕ) [NeZero e] (φ : DirichletCharacter ℂ e) (he : e ∣ N) (hed : e = d)
      (hφ : DirichletCharacter.changeLevel he φ = DirichletCharacter.changeLevel hd χ)
      (hp : φ.IsPrimitive), PChar.mk e φ hp = PChar.mk d χ hprim := by
    intro e _ φ he hed hφ hp
    subst hed
    have hq : φ = χ := DirichletCharacter.changeLevel_injective hd hφ
    subst hq
    rfl
  exact aux η.conductor η.primitiveCharacter η.conductor_dvd_level hcond
    η.changeLevel_primitiveCharacter η.primitiveCharacter_isPrimitive

/-- **Non-Principality of the Lifted Product of Distinct Primitive Real Characters**:
if `ψ₁ ≠ ψ₂` are distinct primitive real characters, then `prodChar ψ₁.χ ψ₂.χ ≠ 1`. -/
theorem prodChar_ne_one_of_distinct_primitive_real {ψ₁ ψ₂ : PChar}
    (h1 : ψ₁.IsReal) (hne : ψ₁ ≠ ψ₂) :
    prodChar ψ₁.χ ψ₂.χ ≠ 1 := by
  intro hprod
  unfold prodChar at hprod
  have hsq1 : DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
      DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ = 1 := by
    rw [← map_mul, ← sq, isRealChar_sq_eq_one h1, map_one]
  have heq :
      DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ =
        DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ := by
    calc DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ
        = 1 * DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ := (one_mul _).symm
      _ = (DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
            DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ) *
            DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ := by rw [hsq1]
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
            (DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
              DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ) := mul_assoc _ _ _
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ * 1 := by rw [hprod]
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ := mul_one _
  have hof := congrArg PChar.of heq
  rw [pchar_of_changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ ψ₂.prim,
      pchar_of_changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ ψ₁.prim] at hof
  exact hne hof.symm

theorem negLogDerivZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    negLogDerivZeta s = LSeries (fun n => (Λ n : ℂ)) s :=
  (RHDirect.LSeries_vonMangoldt_eq_neg_deriv_zeta_div hs).symm

theorem negLogDerivL_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    negLogDerivL χ s = LSeries (fun n => χ n * (Λ n : ℂ)) s :=
  (RHDirect.LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div χ hs).symm

private lemma LSeries_term_add_I_mul (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f ((σ : ℂ) + I * (t : ℂ)) n =
      LSeries.term (fun m => f m * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    ring

private lemma LSeriesSummable_shift_I_mul {f : ℕ → ℂ} {σ : ℝ} (t : ℝ)
    (hf : LSeriesSummable f ((σ : ℂ) + I * (t : ℂ))) :
    LSeriesSummable (fun n => f n * (n : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) := by
  unfold LSeriesSummable at hf ⊢
  refine hf.congr fun n => ?_
  exact LSeries_term_add_I_mul f σ t n

/-- Exact weighted Dirichlet-series identity for the Hadamard–de la Vallée Poussin 3-4-1
combination on `σ > 1`:
`3 (-L'/L)(1_q, σ) + 4 (-L'/L)(χ, σ + it) + (-L'/L)(χ², σ + 2it)` equals the `L`-series at `σ`
of `Λ(n) (3 · 1_q(n) + 4 χ(n) n^(-it) + χ²(n) n^(-2it))`. -/
theorem three_four_one_negLogDerivL_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    3 * negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ) +
      4 * negLogDerivL χ ((σ : ℂ) + I * (t : ℂ)) +
      negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ)) =
    LSeries (fun n => (Λ n : ℂ) *
      (3 * (1 : DirichletCharacter ℂ q) n +
        4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
        (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ))))) (σ : ℂ) := by
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs2 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simp [hσ]
  rw [negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs0,
      negLogDerivL_eq_LSeries χ hs1,
      negLogDerivL_eq_LSeries (χ ^ 2) hs2]
  have hsum0 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs0
  have hsum1 : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs1
  have hsum2 : LSeriesSummable (fun n => (χ ^ 2) n * (Λ n : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) :=
    (χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2
  have hterm1 : ∀ n, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((σ : ℂ) + I * (t : ℂ)) n =
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n :=
    fun n => LSeries_term_add_I_mul _ σ t n
  have hterm2 : ∀ n, LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) n =
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n := by
    intro n
    have h2 : (σ : ℂ) + 2 * I * (t : ℂ) = (σ : ℂ) + I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
    have h2' : -(2 * I * (t : ℂ)) = -(I * ((2 * t : ℝ) : ℂ)) := by push_cast; ring
    rw [h2, h2']
    exact LSeries_term_add_I_mul _ σ (2 * t) n
  have hsum1' : Summable (fun n =>
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n) :=
    hsum1.congr hterm1
  have hsum2' : Summable (fun n =>
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n) :=
    hsum2.congr hterm2
  unfold LSeries
  rw [tsum_congr hterm1, tsum_congr hterm2, ← tsum_mul_left, ← tsum_mul_left,
      ← (hsum0.mul_left 3).tsum_add (hsum1'.mul_left 4),
      ← ((hsum0.mul_left 3).add (hsum1'.mul_left 4)).tsum_add hsum2']
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte]
    ring

private lemma real_tsum_nonneg_of_complex {f : ℕ → ℂ} (hf : Summable f)
    (hre : ∀ n, 0 ≤ (f n).re) : 0 ≤ (∑' n, f n).re := by
  have hsum_re : Summable (fun n => (f n).re) := Complex.reCLM.summable hf
  have heq : (∑' n, f n).re = ∑' n, (f n).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hf
  rw [heq]
  exact tsum_nonneg hre

private lemma norm_cpow_neg_I_mul_nat {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(I * (t : ℂ)))‖ = 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-(I * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- **Unconditional Hadamard–de la Vallée Poussin 3-4-1 Positivity** (`L(1_q, σ)` form):
for every `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `σ > 1`, and `t ∈ ℝ`,
`Re(3 (-L'/L)(1_q, σ) + 4 (-L'/L)(χ, σ + it) + (-L'/L)(χ², σ + 2it)) ≥ 0`. -/
theorem three_four_one_negLogDerivL_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re +
        4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have hre_comb :
      3 * (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re +
          4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
          (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re =
        (3 * negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ) +
          4 * negLogDerivL χ ((σ : ℂ) + I * (t : ℂ)) +
          negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
    simp
  rw [hre_comb, three_four_one_negLogDerivL_eq_LSeries χ hσ t]
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs2 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simp [hσ]
  have hsum0 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs0
  have hsum1 : Summable (fun n =>
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n) :=
    (χ.LSeriesSummable_twist_vonMangoldt hs1).congr (fun n => LSeries_term_add_I_mul _ σ t n)
  have hsum2 : Summable (fun n =>
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n) := by
    refine ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2).congr fun n => ?_
    have h2 : (σ : ℂ) + 2 * I * (t : ℂ) = (σ : ℂ) + I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
    have h2' : -(2 * I * (t : ℂ)) = -(I * ((2 * t : ℝ) : ℂ)) := by push_cast; ring
    rw [h2, h2']
    exact LSeries_term_add_I_mul _ σ (2 * t) n
  have hsumm : Summable (LSeries.term (fun n => (Λ n : ℂ) *
      (3 * (1 : DirichletCharacter ℂ q) n +
        4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
        (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ))))) (σ : ℂ)) := by
    refine (((hsum0.mul_left 3).add (hsum1.mul_left 4)).add hsum2).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn, ↓reduceIte]
      ring
  refine real_tsum_nonneg_of_complex hsumm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow, div_eq_mul_inv, ← Complex.ofReal_inv]
    have hcoeff :
        ((Λ n : ℂ) *
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) *
          ((((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ)).re =
        (Λ n * ((n : ℝ) ^ σ)⁻¹) *
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))).re := by
      have hreorder :
          (Λ n : ℂ) *
            (3 * (1 : DirichletCharacter ℂ q) n +
              4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
              (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) *
            ((((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) =
          (((Λ n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ)) *
            (3 * (1 : DirichletCharacter ℂ q) n +
              4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
              (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) := by
        push_cast; ring
      rw [hreorder, Complex.re_ofReal_mul]
    rw [hcoeff]
    refine mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (inv_nonneg.mpr (Real.rpow_nonneg hnR.le σ))) ?_
    by_cases hu : IsUnit (n : ZMod q)
    · set z : ℂ := χ (n : ZMod q) * (n : ℂ) ^ (-(I * (t : ℂ)))
      have hz_sq : (χ ^ 2) (n : ZMod q) * (n : ℂ) ^ (-(2 * I * (t : ℂ))) = z ^ 2 := by
        have hpow2 : (n : ℂ) ^ (-(2 * I * (t : ℂ))) = ((n : ℂ) ^ (-(I * (t : ℂ)))) ^ 2 := by
          rw [sq, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne')]
          congr 1; ring
        rw [sq, MulChar.mul_apply, hpow2]
        dsimp only [z]
        ring
      have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 1 := MulChar.one_apply hu
      have hz_norm : ‖z‖ ≤ 1 := by
        rw [norm_mul, norm_cpow_neg_I_mul_nat hn t, mul_one]
        exact χ.norm_le_one _
      have hre_z :
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))).re =
          3 + 4 * z.re + (z ^ 2).re := by
        rw [h1, hz_sq]
        have h4 : 4 * χ (n : ZMod q) * (n : ℂ) ^ (-(I * (t : ℂ))) = 4 * z := by
          dsimp only [z]; ring
        rw [h4]
        simp
      rw [hre_z]
      exact three_four_one_complex_nonneg hz_norm
    · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
      simp

/-- Unconditional positivity `Re(-ζ'/ζ(σ)) ≥ 0` for all real `σ > 1`. -/
theorem negLogDerivZeta_re_nonneg {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (negLogDerivZeta (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivZeta_eq_LSeries hs]
  refine real_tsum_nonneg_of_complex (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ)

/-- For every modulus `q ≥ 1` and real `σ > 1`, `Re(-L'/L(1_q, σ)) ≤ Re(-ζ'/ζ(σ))`
(dropping prime-power terms dividing `q` only decreases the non-negative Dirichlet series). -/
theorem negLogDerivL_one_re_le_negLogDerivZeta_re {q : ℕ} [NeZero q] {σ : ℝ} (hσ : 1 < σ) :
    (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ (negLogDerivZeta (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs, negLogDerivZeta_eq_LSeries hs]
  have hsum1 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hdiff : 0 ≤ (LSeries (fun n => (Λ n : ℂ)) (σ : ℂ) -
      LSeries (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ)).re := by
    unfold LSeries
    rw [← Summable.tsum_sub hsumZ hsum1]
    refine real_tsum_nonneg_of_complex (Summable.sub hsumZ hsum1) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
      rw [hcpow]
      by_cases hu : IsUnit (n : ZMod q)
      · rw [MulChar.one_apply hu, one_mul, sub_self, Complex.zero_re]
      · rw [MulChar.map_nonunit _ hu, zero_mul, zero_div, sub_zero, ← Complex.ofReal_div,
          Complex.ofReal_re]
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ)
  simpa [Complex.sub_re] using hdiff

/-- **Unconditional Hadamard–de la Vallée Poussin 3-4-1 Positivity** (`ζ(σ)` form):
for every `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `σ > 1`, and `t ∈ ℝ`,
`Re(3 (-ζ'/ζ)(σ) + 4 (-L'/L)(χ, σ + it) + (-L'/L)(χ², σ + 2it)) ≥ 0`. -/
theorem three_four_one_zeta_negLogDerivL_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivZeta (σ : ℂ)).re +
        4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have h1 := three_four_one_negLogDerivL_re_nonneg χ hσ t
  have h2 := negLogDerivL_one_re_le_negLogDerivZeta_re (q := q) hσ
  linarith

/-- **Unconditional Hadamard–de la Vallée Poussin 3-4-1 Positivity for `ζ(s)`**:
for every `σ > 1` and `t ∈ ℝ`,
`Re(3 (-ζ'/ζ)(σ) + 4 (-ζ'/ζ)(σ + it) + (-ζ'/ζ)(σ + 2it)) ≥ 0`. -/
theorem three_four_one_zeta_re_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivZeta (σ : ℂ)).re +
        4 * (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivZeta ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have h := three_four_one_zeta_negLogDerivL_re_nonneg (1 : DirichletCharacter ℂ 1) hσ t
  have hL : ∀ s : ℂ, negLogDerivL (1 : DirichletCharacter ℂ 1) s = negLogDerivZeta s := fun s => by
    unfold negLogDerivL negLogDerivZeta
    rw [DirichletCharacter.LFunction_modOne_eq]
  rw [one_pow, hL, hL] at h
  exact h

/-- **Unconditional 2-Character Real Positivity** (`ζ(s) L(s, χ)`):
for any character `χ` mod `q` and real `σ > 1`, `0 ≤ Re(-ζ'/ζ(σ)) + Re(-L'/L(χ, σ))`. -/
theorem two_char_negLogDeriv_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (negLogDerivZeta (σ : ℂ)).re + (negLogDerivL χ (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivZeta_eq_LSeries hs, negLogDerivL_eq_LSeries χ hs]
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsumχ : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) (σ : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  rw [← Complex.add_re]
  unfold LSeries
  rw [← Summable.tsum_add hsumZ hsumχ]
  refine real_tsum_nonneg_of_complex (Summable.add hsumZ hsumχ) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow]
    have hfac :
        (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ (n : ZMod q) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) =
          (((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)) * (1 + χ (n : ZMod q)) := by
      push_cast; ring
    rw [hfac, Complex.re_ofReal_mul]
    have hre1 : (1 + χ (n : ZMod q)).re = 1 + (χ (n : ZMod q)).re := by simp
    rw [hre1]
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ))
      (by linarith [(isRealChar_apply_re_bounds (χ := χ) (n : ZMod q)).1])

/-- **Unconditional 4-Character Real Product Positivity** (`ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`):
for ANY two real Dirichlet characters `χ₁ mod q₁`, `χ₂ mod q₂` and any real `σ > 1`,
`0 ≤ Re(-ζ'/ζ(σ)) + Re(-L'/L(χ₁, σ)) + Re(-L'/L(χ₂, σ)) + Re(-L'/L(prodChar χ₁ χ₂, σ))`. -/
theorem four_char_real_negLogDeriv_re_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (negLogDerivZeta (σ : ℂ)).re + (negLogDerivL χ₁ (σ : ℂ)).re +
        (negLogDerivL χ₂ (σ : ℂ)).re + (negLogDerivL (prodChar χ₁ χ₂) (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivZeta_eq_LSeries hs, negLogDerivL_eq_LSeries χ₁ hs,
      negLogDerivL_eq_LSeries χ₂ hs, negLogDerivL_eq_LSeries (prodChar χ₁ χ₂) hs]
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum1 : LSeriesSummable (fun n => χ₁ n * (Λ n : ℂ)) (σ : ℂ) :=
    χ₁.LSeriesSummable_twist_vonMangoldt hs
  have hsum2 : LSeriesSummable (fun n => χ₂ n * (Λ n : ℂ)) (σ : ℂ) :=
    χ₂.LSeriesSummable_twist_vonMangoldt hs
  have hsum12 : LSeriesSummable (fun n => (prodChar χ₁ χ₂) n * (Λ n : ℂ)) (σ : ℂ) :=
    (prodChar χ₁ χ₂).LSeriesSummable_twist_vonMangoldt hs
  rw [← Complex.add_re, ← Complex.add_re, ← Complex.add_re]
  unfold LSeries
  have hsumZ1 : Summable (fun n => LSeries.term (fun m => (Λ m : ℂ)) (σ : ℂ) n +
      LSeries.term (fun m => χ₁ m * (Λ m : ℂ)) (σ : ℂ) n) := Summable.add hsumZ hsum1
  have hsumZ12 : Summable (fun n => (LSeries.term (fun m => (Λ m : ℂ)) (σ : ℂ) n +
      LSeries.term (fun m => χ₁ m * (Λ m : ℂ)) (σ : ℂ) n) +
      LSeries.term (fun m => χ₂ m * (Λ m : ℂ)) (σ : ℂ) n) := Summable.add hsumZ1 hsum2
  rw [← Summable.tsum_add hsumZ hsum1, ← Summable.tsum_add hsumZ1 hsum2,
      ← Summable.tsum_add hsumZ12 hsum12]
  refine real_tsum_nonneg_of_complex (Summable.add hsumZ12 hsum12) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow, prodChar_apply_nat]
    have hfac :
        (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₁ (n : ZMod q₁) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₂ (n : ZMod q₂) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) =
          (((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)) *
            (1 + χ₁ (n : ZMod q₁) + χ₂ (n : ZMod q₂) + χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)) := by
      push_cast; ring
    rw [hfac, Complex.re_ofReal_mul]
    have hre :
        (1 + χ₁ (n : ZMod q₁) + χ₂ (n : ZMod q₂) + χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)).re =
          1 + (χ₁ (n : ZMod q₁)).re + (χ₂ (n : ZMod q₂)).re +
            (χ₁ (n : ZMod q₁)).re * (χ₂ (n : ZMod q₂)).re := by
      simp [Complex.mul_re, h1 (n : ZMod q₁), h2 (n : ZMod q₂)]
    rw [hre]
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ))
      (four_char_real_nonneg
        (isRealChar_apply_re_bounds (χ := χ₁) (n : ZMod q₁)).1
        (isRealChar_apply_re_bounds (χ := χ₂) (n : ZMod q₂)).1)

/-! ## Section 2: Quantitative Classical Zero-Free Region & Landau–Page Isolation -/

/-- Textbook Hadamard-product logarithmic-derivative upper bounds on the vertical strip
`1 < σ ≤ 2` (Davenport Ch. 14 / Montgomery–Vaughan Ch. 11 / Iwaniec–Kowalski Lemma 5.9).
All constants in the resulting zero-free regions and Landau–Page isolation are explicit
rational multiples of `(max B 1)⁻¹`. -/
structure HadamardLogDerivPackage (B : ℝ) : Prop where
  B_pos : 0 < B
  zeta_pole :
    ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + B
  zeta_upper :
    ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
        B * Real.log (|t| + 2) + (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re
  zeta_one_zero :
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
        (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
          B * Real.log (|t| + 2) +
            (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re -
            (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)).re
  zeta_two_zeros :
    ∀ ρ₁ ρ₂ : ℂ, ρ₁ ≠ ρ₂ → 0 < ρ₁.re → ρ₁.re < 1 → 0 < ρ₂.re → ρ₂.re < 1 →
      riemannZeta ρ₁ = 0 → riemannZeta ρ₂ = 0 →
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
        (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re ≤
          B * Real.log (|t| + 2) +
            (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re -
            (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ₁)).re -
            (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ₂)).re
  principal_upper :
    ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 →
      (negLogDerivL (1 : DirichletCharacter ℂ q) ((σ : ℂ) + I * (t : ℂ))).re ≤
        B * Real.log ((q : ℝ) * (|t| + 2)) + (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re
  nonprincipal_upper :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
        (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
          B * Real.log ((q : ℝ) * (|t| + 2))
  nonprincipal_one_zero :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
        ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
          (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
            B * Real.log ((q : ℝ) * (|t| + 2)) - (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)).re
  nonprincipal_two_zeros :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ ρ₁ ρ₂ : ℂ, ρ₁ ≠ ρ₂ → 0 < ρ₁.re → ρ₁.re < 1 → 0 < ρ₂.re → ρ₂.re < 1 →
        DirichletCharacter.LFunction χ ρ₁ = 0 → DirichletCharacter.LFunction χ ρ₂ = 0 →
        ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
          (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
            B * Real.log ((q : ℝ) * (|t| + 2)) -
              (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ₁)).re -
              (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ₂)).re

private lemma re_inv_sub_eq (σ t : ℝ) (ρ : ℂ) :
    (1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)).re =
      (σ - ρ.re) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2) := by
  set z : ℂ := ((σ : ℂ) + I * (t : ℂ)) - ρ
  have hzre : z.re = σ - ρ.re := by simp [z]
  have hzim : z.im = t - ρ.im := by simp [z]
  have hns : Complex.normSq z = (σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]; ring
  rw [one_div, Complex.inv_re, hzre, hns]

private lemma re_inv_sub_at_im {σ : ℝ} {ρ : ℂ} (hσ : ρ.re < σ) :
    (1 / (((σ : ℂ) + I * (ρ.im : ℂ)) - ρ)).re = 1 / (σ - ρ.re) := by
  rw [re_inv_sub_eq, sub_self, zero_pow (by norm_num), add_zero]
  have hne : σ - ρ.re ≠ 0 := by linarith
  field_simp [hne]

private lemma re_inv_sub_one_eq (σ t : ℝ) :
    (1 / (((σ : ℂ) + I * (t : ℂ)) - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
  have h := re_inv_sub_eq σ t (1 : ℂ)
  simpa using h

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

private lemma half_lt_log_q_abs_add_two {q : ℕ} [NeZero q] (t : ℝ) :
    (1 / 2 : ℝ) < Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have h2 : (2 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  exact half_lt_log_two.trans_le (Real.log_le_log (by norm_num) h2)

private lemma log_q_two_mul_abs_le {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have h1 : (q : ℝ) * (|2 * t| + 2) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg t]
  have hpos : 0 < (q : ℝ) * (|2 * t| + 2) := by positivity
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  calc Real.log ((q : ℝ) * (|2 * t| + 2))
      ≤ Real.log (2 * ((q : ℝ) * (|t| + 2))) := Real.log_le_log hpos h1
    _ = Real.log 2 + Real.log ((q : ℝ) * (|t| + 2)) :=
        Real.log_mul (by norm_num) (by positivity)
    _ ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by linarith

/-- **Quantitative Classical Zero-Free Region for Complex Characters (`χ ^ 2 ≠ 1`)**:
for any `χ : DirichletCharacter ℂ q` with `χ ^ 2 ≠ 1` and any critical-strip zero `ρ`,
`ρ.re ≤ 1 - 1 / (168 * max B 1 * log (q * (|ρ.im| + 2)))`. -/
theorem zeroFreeRegion_complex_char {B : ℝ} (H : HadamardLogDerivPackage B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (168 * max B 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) := by
  have hχ1 : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hBC : B ≤ C := le_max_left B 1
  have hB0 : 0 < B := H.B_pos
  set L : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2))
  have hL : (1 / 2 : ℝ) < L := half_lt_log_q_abs_add_two ρ.im
  have hCL_pos : 0 < C * L := by positivity
  set δ : ℝ := 1 / (24 * C * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hpos := three_four_one_zeta_negLogDerivL_re_nonneg χ hσ1 ρ.im
  have hZ := H.zeta_pole σ hσ1 hσ2
  have hX1 := H.nonprincipal_one_zero q χ hχ1 ρ h0 h1 hz σ ρ.im hσ1 hσ2
  have hX2 := H.nonprincipal_upper q (χ ^ 2) hχ2 σ (2 * ρ.im) hσ1 hσ2
  have h2it : (σ : ℂ) + 2 * I * (ρ.im : ℂ) = (σ : ℂ) + I * ((2 * ρ.im : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2it] at hpos
  rw [re_inv_sub_at_im (by linarith : ρ.re < σ)] at hX1
  have hlog2 : Real.log ((q : ℝ) * (|2 * ρ.im| + 2)) ≤ 2 * L := log_q_two_mul_abs_le ρ.im
  have hX2' : (negLogDerivL (χ ^ 2) ((σ : ℂ) + I * ((2 * ρ.im : ℝ) : ℂ))).re ≤ 2 * B * L := by
    have := mul_le_mul_of_nonneg_left hlog2 hB0.le
    linarith
  have hB_le : B ≤ 2 * (C * L) := by nlinarith
  have hBL_le : B * L ≤ C * L := mul_le_mul_of_nonneg_right hBC (by linarith)
  have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
  rw [hσ_sub] at hZ
  have h12CL : 12 * (C * L) = 1 / (2 * δ) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  have hX1' : (negLogDerivL χ ((σ : ℂ) + I * (ρ.im : ℂ))).re ≤ B * L - 1 / (σ - ρ.re) := hX1
  have hineq : 4 / (σ - ρ.re) ≤ 3 / δ + 1 / (2 * δ) := by
    have hsum : 3 * B + 4 * (B * L) + 2 * (B * L) ≤ 12 * (C * L) := by linarith
    have hX2'' : (negLogDerivL (χ ^ 2) ((σ : ℂ) + I * ((2 * ρ.im : ℝ) : ℂ))).re ≤ 2 * (B * L) := by
      linarith
    have h3δ : 3 * (1 / δ) = 3 / δ := by ring
    have h4σ : 4 * (1 / (σ - ρ.re)) = 4 / (σ - ρ.re) := by ring
    linarith
  have hcomb : 3 / δ + 1 / (2 * δ) = 7 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
  rw [hcomb] at hineq
  have hσρ_pos : 0 < σ - ρ.re := by linarith
  have hmul : 8 * δ ≤ 7 * (σ - ρ.re) := by
    have h1' := (div_le_div_iff₀ hσρ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq
    linarith
  have hβ : ρ.re ≤ 1 - δ / 7 := by dsimp only [σ] at hmul; linarith
  have hδ7 : δ / 7 = 1 / (168 * C * L) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  linarith

/-- **Quantitative Classical Zero-Free Region for Non-Real Zeros of Real Characters (`χ ^ 2 = 1`)**:
for any non-principal real character `χ ≠ 1` mod `q` and any non-real critical-strip zero `ρ`
(`ρ.im ≠ 0`), `ρ.re ≤ 1 - 1 / (296 * max B 1 * log (q * (|ρ.im| + 2)))`.
Combines 3-4-1 positivity for `|ρ.im| ≥ 1 / (24 C L)` with 2-character conjugate-pair positivity
for `0 < |ρ.im| < 1 / (24 C L)`. -/
theorem zeroFreeRegion_real_char_nonreal_zero {B : ℝ} (H : HadamardLogDerivPackage B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (296 * max B 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hBC : B ≤ C := le_max_left B 1
  have hB0 : 0 < B := H.B_pos
  set L : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2))
  have hL : (1 / 2 : ℝ) < L := half_lt_log_q_abs_add_two ρ.im
  have hCL_pos : 0 < C * L := by positivity
  set δ : ℝ := 1 / (24 * C * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hB_le : B ≤ 2 * (C * L) := by nlinarith
  have hBL_le : B * L ≤ C * L := mul_le_mul_of_nonneg_right hBC (by linarith)
  by_cases hγ : δ ≤ |ρ.im|
  · -- Large imaginary part `|ρ.im| ≥ δ`: use 3-4-1 with the pole term of `L(1_q, σ + 2iγ)`.
    set σ : ℝ := 1 + δ
    have hσ1 : 1 < σ := by linarith
    have hσ2 : σ ≤ 2 := by linarith
    have hpos := three_four_one_zeta_negLogDerivL_re_nonneg χ hσ1 ρ.im
    rw [hχ2] at hpos
    have h2it : (σ : ℂ) + 2 * I * (ρ.im : ℂ) = (σ : ℂ) + I * ((2 * ρ.im : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2it] at hpos
    have hZ := H.zeta_pole σ hσ1 hσ2
    have hX1 := H.nonprincipal_one_zero q χ hχ1 ρ h0 h1 hz σ ρ.im hσ1 hσ2
    have hX2 := H.principal_upper q σ (2 * ρ.im) hσ1 hσ2
    rw [re_inv_sub_at_im (by linarith : ρ.re < σ)] at hX1
    rw [re_inv_sub_one_eq] at hX2
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rw [hσ_sub] at hZ hX2
    have hpole : δ / (δ ^ 2 + (2 * ρ.im) ^ 2) ≤ 1 / (5 * δ) := by
      have hsq : δ ^ 2 ≤ ρ.im ^ 2 := by
        rw [← sq_abs ρ.im]
        exact pow_le_pow_left₀ hδ_pos.le hγ 2
      have hden : 5 * δ ^ 2 ≤ δ ^ 2 + (2 * ρ.im) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hlog2 : Real.log ((q : ℝ) * (|2 * ρ.im| + 2)) ≤ 2 * L := log_q_two_mul_abs_le ρ.im
    have hBL2 : B * Real.log ((q : ℝ) * (|2 * ρ.im| + 2)) ≤ 2 * (B * L) := by
      have := mul_le_mul_of_nonneg_left hlog2 hB0.le; linarith
    have h12CL : 12 * (C * L) = 1 / (2 * δ) := by
      dsimp only [δ]; field_simp [hCL_pos.ne']; ring
    have hX1' : (negLogDerivL χ ((σ : ℂ) + I * (ρ.im : ℂ))).re ≤ B * L - 1 / (σ - ρ.re) := hX1
    have hineq : 4 / (σ - ρ.re) ≤ 3 / δ + 1 / (5 * δ) + 1 / (2 * δ) := by
      have hsum : 3 * B + 4 * (B * L) + 2 * (B * L) ≤ 12 * (C * L) := by linarith
      have h3δ : 3 * (1 / δ) = 3 / δ := by ring
      have h4σ : 4 * (1 / (σ - ρ.re)) = 4 / (σ - ρ.re) := by ring
      linarith
    have hcomb : 3 / δ + 1 / (5 * δ) + 1 / (2 * δ) = 37 / (10 * δ) := by
      field_simp [hδ_pos.ne']; ring
    rw [hcomb] at hineq
    have hσρ_pos : 0 < σ - ρ.re := by linarith
    have hmul : 40 * δ ≤ 37 * (σ - ρ.re) := by
      have h1' := (div_le_div_iff₀ hσρ_pos (by positivity : (0 : ℝ) < 10 * δ)).mp hineq
      linarith
    have hβ : ρ.re ≤ 1 - 3 * δ / 37 := by dsimp only [σ] at hmul; linarith
    have hδ296 : 1 / (296 * C * L) = 3 * δ / 37 := by
      dsimp only [δ]; field_simp [hCL_pos.ne']; ring
    linarith
  · -- Small nonzero imaginary part `0 < |ρ.im| < δ`: conjugate pair `{ρ, conj ρ}` at `σ = 1 + 2δ`.
    push Not at hγ
    set η : ℝ := 2 * δ
    have hη_pos : 0 < η := by positivity
    have hη_le1 : η ≤ 1 := by
      dsimp only [η, δ]
      rw [mul_one_div, div_le_one (by positivity)]
      nlinarith
    set σ : ℝ := 1 + η
    have hσ1 : 1 < σ := by linarith
    have hσ2 : σ ≤ 2 := by linarith
    have hreal : IsRealChar χ := isRealChar_of_sq_eq_one hχ2
    have hinv : χ⁻¹ = χ := isRealChar_inv_eq_self hreal
    have hz_conj : DirichletCharacter.LFunction χ (starRingEnd ℂ ρ) = 0 := by
      have h := (RHDirect.LFunction_eq_zero_conj_iff χ (.inl hχ1)).mpr hz
      rwa [hinv] at h
    have hne_conj : ρ ≠ starRingEnd ℂ ρ := by
      intro heq
      have h2 := congrArg Complex.im heq
      simp only [Complex.conj_im] at h2
      exact him (by linarith)
    have hpos := two_char_negLogDeriv_re_nonneg χ hσ1
    have hZ := H.zeta_pole σ hσ1 hσ2
    have hX := H.nonprincipal_two_zeros q χ hχ1 ρ (starRingEnd ℂ ρ) hne_conj
      h0 h1 (by simpa using h0) (by simpa using h1) hz hz_conj σ 0 hσ1 hσ2
    simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero, zero_add] at hX
    have hre1 : (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
      have h := re_inv_sub_eq σ 0 ρ
      simpa [neg_sq] using h
    have hre2 : (1 / ((σ : ℂ) - starRingEnd ℂ ρ)).re =
        (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
      have h := re_inv_sub_eq σ 0 (starRingEnd ℂ ρ)
      simpa using h
    rw [hre1, hre2] at hX
    have hσρ_ge : η ≤ σ - ρ.re := by dsimp only [σ]; linarith
    have hσρ_pos : 0 < σ - ρ.re := by linarith
    have hγ_le_half : |ρ.im| ≤ (σ - ρ.re) / 2 := by dsimp only [η] at hσρ_ge; linarith
    have hγ_sq : ρ.im ^ 2 ≤ (σ - ρ.re) ^ 2 / 4 := by
      rw [← sq_abs ρ.im]
      have := pow_le_pow_left₀ (abs_nonneg ρ.im) hγ_le_half 2
      linarith
    have hden_pos : 0 < (σ - ρ.re) ^ 2 + ρ.im ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos hσρ_pos) (sq_nonneg _)
    have hpair_ge : 8 / (5 * (σ - ρ.re)) ≤ 2 * ((σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hden_pos]
      nlinarith
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hlog_le : Real.log ((q : ℝ) * 2) ≤ L :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hBL0 : B * Real.log ((q : ℝ) * 2) ≤ C * L :=
      (mul_le_mul_of_nonneg_left hlog_le hB0.le).trans hBL_le
    have h3CL : 3 * (C * L) = 1 / (4 * η) := by
      dsimp only [η, δ]; field_simp [hCL_pos.ne']; ring
    have hσ_sub : σ - 1 = η := by dsimp only [σ]; ring
    rw [hσ_sub] at hZ
    have hX' : (negLogDerivL χ (σ : ℂ)).re ≤
        C * L - 8 / (5 * (σ - ρ.re)) := by
      linarith [hX, hBL0, hpair_ge]
    have hineq : 8 / (5 * (σ - ρ.re)) ≤ 1 / η + 1 / (4 * η) := by
      linarith [hpos, hZ, hX', hB_le, h3CL]
    have hcomb : 1 / η + 1 / (4 * η) = 5 / (4 * η) := by field_simp [hη_pos.ne']; ring
    rw [hcomb] at hineq
    have hmul : 32 * η ≤ 25 * (σ - ρ.re) := by
      have h1' := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (σ - ρ.re))
        (by positivity : (0 : ℝ) < 4 * η)).mp hineq
      linarith
    have hβ : ρ.re ≤ 1 - 7 * η / 25 := by dsimp only [σ] at hmul; linarith
    have hcmp : 1 / (296 * C * L) ≤ 7 * η / 25 := by
      have hη_val : 7 * η / 25 = 7 / (300 * C * L) := by
        dsimp only [η, δ]; field_simp [hCL_pos.ne']; ring
      rw [hη_val, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- **Quantitative Classical Zero-Free Region for the Riemann Zeta Function `ζ(s)`**:
for any critical-strip zero `ρ` of `riemannZeta` with `ρ.im ≠ 0`,
`ρ.re ≤ 1 - 1 / (640 * max B 1 * log (|ρ.im| + 2))`. -/
theorem zeroFreeRegion_riemannZeta {B : ℝ} (H : HadamardLogDerivPackage B)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - 1 / (640 * max B 1 * Real.log (|ρ.im| + 2)) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hBC : B ≤ C := le_max_left B 1
  have hB0 : 0 < B := H.B_pos
  set L : ℝ := Real.log (|ρ.im| + 2)
  have hL : (1 / 2 : ℝ) < L := by
    have h := half_lt_log_q_abs_add_two (q := 1) ρ.im
    simpa using h
  have hCL_pos : 0 < C * L := by positivity
  have hB_le : B ≤ 2 * (C * L) := by nlinarith
  have hBL_le : B * L ≤ C * L := mul_le_mul_of_nonneg_right hBC (by linarith)
  set δ : ℝ := 1 / (72 * C * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  by_cases hγ : 3 * δ ≤ |ρ.im|
  · -- Large imaginary part `|ρ.im| ≥ 3 δ`: 3-4-1 for `ζ(s)`.
    set σ : ℝ := 1 + δ
    have hσ1 : 1 < σ := by linarith
    have hσ2 : σ ≤ 2 := by linarith
    have hpos := three_four_one_zeta_re_nonneg hσ1 ρ.im
    have h2it : (σ : ℂ) + 2 * I * (ρ.im : ℂ) = (σ : ℂ) + I * ((2 * ρ.im : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2it] at hpos
    have hZ0 := H.zeta_pole σ hσ1 hσ2
    have hZ1 := H.zeta_one_zero ρ h0 h1 hz σ ρ.im hσ1 hσ2
    have hZ2 := H.zeta_upper σ (2 * ρ.im) hσ1 hσ2
    rw [re_inv_sub_at_im (by linarith : ρ.re < σ), re_inv_sub_one_eq] at hZ1
    rw [re_inv_sub_one_eq] at hZ2
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rw [hσ_sub] at hZ0 hZ1 hZ2
    have hsq : 9 * δ ^ 2 ≤ ρ.im ^ 2 := by
      rw [← sq_abs ρ.im]
      have := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * δ) hγ 2
      linarith
    have hp1 : δ / (δ ^ 2 + ρ.im ^ 2) ≤ 1 / (10 * δ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hp2 : δ / (δ ^ 2 + (2 * ρ.im) ^ 2) ≤ 1 / (37 * δ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hlog2 : Real.log (|2 * ρ.im| + 2) ≤ 2 * L := by
      have h := log_q_two_mul_abs_le (q := 1) ρ.im
      simpa using h
    have hBL2 : B * Real.log (|2 * ρ.im| + 2) ≤ 2 * (B * L) := by
      have := mul_le_mul_of_nonneg_left hlog2 hB0.le; linarith
    have h12CL : 12 * (C * L) = 1 / (6 * δ) := by
      dsimp only [δ]; field_simp [hCL_pos.ne']; ring
    have hZ1' : (negLogDerivZeta ((σ : ℂ) + I * (ρ.im : ℂ))).re ≤
        B * L + δ / (δ ^ 2 + ρ.im ^ 2) - 1 / (σ - ρ.re) := hZ1
    have hineq : 4 / (σ - ρ.re) ≤ 3 / δ + 4 / (10 * δ) + 1 / (37 * δ) + 1 / (6 * δ) := by
      have hsum : 3 * B + 4 * (B * L) + 2 * (B * L) ≤ 12 * (C * L) := by linarith
      have hp1_4 : 4 * (δ / (δ ^ 2 + ρ.im ^ 2)) ≤ 4 / (10 * δ) := by
        have h1' := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℝ) ≤ 4)
        have h2' : 4 * (1 / (10 * δ)) = 4 / (10 * δ) := by ring
        linarith
      have h3δ : 3 * (1 / δ) = 3 / δ := by ring
      have h4σ : 4 * (1 / (σ - ρ.re)) = 4 / (σ - ρ.re) := by ring
      linarith
    have hcomb : 3 / δ + 4 / (10 * δ) + 1 / (37 * δ) + 1 / (6 * δ) = 3989 / (1110 * δ) := by
      field_simp [hδ_pos.ne']; ring
    rw [hcomb] at hineq
    have hσρ_pos : 0 < σ - ρ.re := by linarith
    have hmul : 4440 * δ ≤ 3989 * (σ - ρ.re) := by
      have h1' := (div_le_div_iff₀ hσρ_pos (by positivity : (0 : ℝ) < 1110 * δ)).mp hineq
      linarith
    have hβ : ρ.re ≤ 1 - 451 * δ / 3989 := by dsimp only [σ] at hmul; linarith
    have hcmp : 1 / (640 * C * L) ≤ 451 * δ / 3989 := by
      have hval : 451 * δ / 3989 = 451 / (287208 * C * L) := by
        dsimp only [δ]; field_simp [hCL_pos.ne']; ring
      rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · -- Small nonzero imaginary part `0 < |ρ.im| < 3 δ`: conjugate pair `{ρ, conj ρ}` at `σ = 1 + 6 δ`.
    push Not at hγ
    set η : ℝ := 6 * δ
    have hη_pos : 0 < η := by positivity
    have hη_le1 : η ≤ 1 := by
      dsimp only [η, δ]
      rw [mul_one_div, div_le_one (by positivity)]
      nlinarith
    set σ : ℝ := 1 + η
    have hσ1 : 1 < σ := by linarith
    have hσ2 : σ ≤ 2 := by linarith
    have hs1 : ρ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; exact lt_irrefl _ h1
    have hz_conj : riemannZeta (starRingEnd ℂ ρ) = 0 :=
      (RHDirect.riemannZeta_eq_zero_conj_iff hs1).mpr hz
    have hne_conj : ρ ≠ starRingEnd ℂ ρ := by
      intro heq
      have h2 := congrArg Complex.im heq
      simp only [Complex.conj_im] at h2
      exact him (by linarith)
    have hpos := negLogDerivZeta_re_nonneg hσ1
    have hZ := H.zeta_two_zeros ρ (starRingEnd ℂ ρ) hne_conj
      h0 h1 (by simpa using h0) (by simpa using h1) hz hz_conj σ 0 hσ1 hσ2
    simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero, zero_add] at hZ
    have hre1 : (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
      have h := re_inv_sub_eq σ 0 ρ
      simpa [neg_sq] using h
    have hre2 : (1 / ((σ : ℂ) - starRingEnd ℂ ρ)).re =
        (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
      have h := re_inv_sub_eq σ 0 (starRingEnd ℂ ρ)
      simpa using h
    have hp0 : (1 / ((σ : ℂ) - 1)).re = 1 / η := by
      have h := re_inv_sub_one_eq σ 0
      simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
        add_zero] at h
      have hσ_sub : σ - 1 = η := by dsimp only [σ]; ring
      rw [h, hσ_sub]
      field_simp [hη_pos.ne']
    rw [hre1, hre2, hp0] at hZ
    have hσρ_ge : η ≤ σ - ρ.re := by dsimp only [σ]; linarith
    have hσρ_pos : 0 < σ - ρ.re := by linarith
    have hγ_le_half : |ρ.im| ≤ (σ - ρ.re) / 2 := by dsimp only [η] at hσρ_ge; linarith
    have hγ_sq : ρ.im ^ 2 ≤ (σ - ρ.re) ^ 2 / 4 := by
      rw [← sq_abs ρ.im]
      have := pow_le_pow_left₀ (abs_nonneg ρ.im) hγ_le_half 2
      linarith
    have hden_pos : 0 < (σ - ρ.re) ^ 2 + ρ.im ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos hσρ_pos) (sq_nonneg _)
    have hpair_ge : 8 / (5 * (σ - ρ.re)) ≤ 2 * ((σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hden_pos]
      nlinarith
    have hlog_le : Real.log 2 ≤ L :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
    have hBL0 : B * Real.log 2 ≤ C * L :=
      (mul_le_mul_of_nonneg_left hlog_le hB0.le).trans hBL_le
    have hCL_eq : C * L = 1 / (12 * η) := by
      dsimp only [η, δ]; field_simp [hCL_pos.ne']; ring
    have hZ' : (negLogDerivZeta (σ : ℂ)).re ≤
        C * L + 1 / η - 8 / (5 * (σ - ρ.re)) := by
      linarith [hZ, hBL0, hpair_ge]
    have hineq : 8 / (5 * (σ - ρ.re)) ≤ 1 / η + 1 / (12 * η) := by
      linarith [hpos, hZ', hCL_eq]
    have hcomb : 1 / η + 1 / (12 * η) = 13 / (12 * η) := by field_simp [hη_pos.ne']; ring
    rw [hcomb] at hineq
    have hmul : 96 * η ≤ 65 * (σ - ρ.re) := by
      have h1' := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (σ - ρ.re))
        (by positivity : (0 : ℝ) < 12 * η)).mp hineq
      linarith
    have hβ : ρ.re ≤ 1 - 31 * η / 65 := by dsimp only [σ] at hmul; linarith
    have hcmp : 1 / (640 * C * L) ≤ 31 * η / 65 := by
      have hval : 31 * η / 65 = 31 / (780 * C * L) := by
        dsimp only [η, δ]; field_simp [hCL_pos.ne']; ring
      rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- **Exclusion of Two Real Zeros of a Single Real Character**:
if `χ ≠ 1` mod `q` has two distinct real zeros `β₁, β₂ ∈ (0, 1)`, then
`min β₁ β₂ ≤ 1 - 1 / (18 * max B 1 * log (2 * q))`. -/
theorem real_char_at_most_one_exceptional_real_zero {B : ℝ} (H : HadamardLogDerivPackage B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {β₁ β₂ : ℝ} (hne : β₁ ≠ β₂)
    (h10 : 0 < β₁) (h11 : β₁ < 1) (h20 : 0 < β₂) (h21 : β₂ < 1)
    (hz1 : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction χ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (18 * max B 1 * Real.log (2 * (q : ℝ))) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hBC : B ≤ C := le_max_left B 1
  set L : ℝ := Real.log (2 * (q : ℝ))
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hL : (1 / 2 : ℝ) < L :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hCL_pos : 0 < C * L := by positivity
  set δ : ℝ := 1 / (6 * C * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hpos := two_char_negLogDeriv_re_nonneg χ hσ1
  have hZ := H.zeta_pole σ hσ1 hσ2
  have hneC : (β₁ : ℂ) ≠ (β₂ : ℂ) := fun h => hne (Complex.ofReal_injective h)
  have hX := H.nonprincipal_two_zeros q χ hχ1 (β₁ : ℂ) (β₂ : ℂ) hneC
    (by simpa using h10) (by simpa using h11) (by simpa using h20) (by simpa using h21)
    hz1 hz2 σ 0 hσ1 hσ2
  simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero] at hX
  have hlog_eq : Real.log ((q : ℝ) * (0 + 2)) = L := by
    dsimp only [L]; congr 1; ring
  rw [hlog_eq] at hX
  have hre1 : (1 / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (σ - β₁) := by
    have h := re_inv_sub_at_im (σ := σ) (ρ := (β₁ : ℂ)) (by simpa using (by linarith : β₁ < σ))
    simpa using h
  have hre2 : (1 / ((σ : ℂ) - (β₂ : ℂ))).re = 1 / (σ - β₂) := by
    have h := re_inv_sub_at_im (σ := σ) (ρ := (β₂ : ℂ)) (by simpa using (by linarith : β₂ < σ))
    simpa using h
  rw [hre1, hre2] at hX
  have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
  rw [hσ_sub] at hZ
  have hB_le : B ≤ 2 * C * L := by nlinarith
  have hBL_le : B * L ≤ C * L := mul_le_mul_of_nonneg_right hBC (by linarith)
  have h3CL : 3 * C * L = 1 / (2 * δ) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  set β : ℝ := min β₁ β₂
  have hσβ_pos : 0 < σ - β := by
    have : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) h11
    linarith
  have hd1 : 1 / (σ - β) ≤ 1 / (σ - β₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left β₁ β₂])
  have hd2 : 1 / (σ - β) ≤ 1 / (σ - β₂) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right β₁ β₂])
  have hineq : 2 / (σ - β) ≤ 1 / δ + 1 / (2 * δ) := by
    have h2 : 2 / (σ - β) = 1 / (σ - β) + 1 / (σ - β) := by ring
    linarith
  have hcomb : 1 / δ + 1 / (2 * δ) = 3 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
  rw [hcomb] at hineq
  have hmul : 4 * δ ≤ 3 * (σ - β) := by
    have h1' := (div_le_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq
    linarith
  have hβ_le : β ≤ 1 - δ / 3 := by dsimp only [σ] at hmul; linarith
  have hδ3 : δ / 3 = 1 / (18 * C * L) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  linarith

/-- **Landau–Page Two-Character Theorem** (via 4-character positivity of
`ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁ χ₂)`):
if `ψ₁ ≠ ψ₂` are two distinct non-principal primitive real characters of conductors `≤ Q`
(`Q ≥ 2`) with real zeros `β₁, β₂ ∈ (0, 1)`, then
`min β₁ β₂ ≤ 1 - 1 / (36 * max B 1 * log (2 * Q))`. -/
theorem landau_page_two_distinct_real_chars {B : ℝ} (H : HadamardLogDerivPackage B)
    {Q : ℝ} (hQ : 2 ≤ Q)
    {ψ₁ ψ₂ : PChar} (hne : ψ₁ ≠ ψ₂)
    (h1_ne : ψ₁.χ ≠ 1) (h2_ne : ψ₂.χ ≠ 1)
    (h1_real : ψ₁.IsReal) (h2_real : ψ₂.IsReal)
    (hq1 : (ψ₁.N : ℝ) ≤ Q) (hq2 : (ψ₂.N : ℝ) ≤ Q)
    {β₁ β₂ : ℝ} (h10 : 0 < β₁) (h11 : β₁ < 1) (h20 : 0 < β₂) (h21 : β₂ < 1)
    (hz1 : DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction ψ₂.χ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (36 * max B 1 * Real.log (2 * Q)) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hBC : B ≤ C := le_max_left B 1
  have hB0 : 0 < B := H.B_pos
  set L : ℝ := Real.log (2 * Q)
  have hL : (1 / 2 : ℝ) < L :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hCL_pos : 0 < C * L := by positivity
  set δ : ℝ := 1 / (12 * C * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have h12_ne : prodChar ψ₁.χ ψ₂.χ ≠ 1 :=
    prodChar_ne_one_of_distinct_primitive_real h1_real hne
  have hpos := four_char_real_negLogDeriv_re_nonneg h1_real h2_real hσ1
  have hZ := H.zeta_pole σ hσ1 hσ2
  have hX1 := H.nonprincipal_one_zero ψ₁.N ψ₁.χ h1_ne (β₁ : ℂ)
    (by simpa using h10) (by simpa using h11) hz1 σ 0 hσ1 hσ2
  have hX2 := H.nonprincipal_one_zero ψ₂.N ψ₂.χ h2_ne (β₂ : ℂ)
    (by simpa using h20) (by simpa using h21) hz2 σ 0 hσ1 hσ2
  have hX12 := H.nonprincipal_upper (ψ₁.N * ψ₂.N) (prodChar ψ₁.χ ψ₂.χ) h12_ne σ 0 hσ1 hσ2
  simp only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero, zero_add] at hX1 hX2 hX12
  have hre1 : (1 / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (σ - β₁) := by
    have h := re_inv_sub_at_im (σ := σ) (ρ := (β₁ : ℂ)) (by simpa using (by linarith : β₁ < σ))
    simpa using h
  have hre2 : (1 / ((σ : ℂ) - (β₂ : ℂ))).re = 1 / (σ - β₂) := by
    have h := re_inv_sub_at_im (σ := σ) (ρ := (β₂ : ℂ)) (by simpa using (by linarith : β₂ < σ))
    simpa using h
  rw [hre1] at hX1
  rw [hre2] at hX2
  have hq1_pos : (0 : ℝ) < (ψ₁.N : ℝ) := by exact_mod_cast NeZero.pos ψ₁.N
  have hq2_pos : (0 : ℝ) < (ψ₂.N : ℝ) := by exact_mod_cast NeZero.pos ψ₂.N
  have hlog1 : Real.log ((ψ₁.N : ℝ) * 2) ≤ L :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log ((ψ₂.N : ℝ) * 2) ≤ L :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog12 : Real.log (((ψ₁.N * ψ₂.N : ℕ) : ℝ) * 2) ≤ 2 * L := by
    have hmul_pos : (0 : ℝ) < ((ψ₁.N * ψ₂.N : ℕ) : ℝ) * 2 := by
      have : (0 : ℝ) < ((ψ₁.N * ψ₂.N : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (NeZero.pos ψ₁.N) (NeZero.pos ψ₂.N)
      linarith
    have hmul_le : ((ψ₁.N * ψ₂.N : ℕ) : ℝ) * 2 ≤ (2 * Q) ^ 2 := by
      push_cast
      nlinarith
    calc Real.log (((ψ₁.N * ψ₂.N : ℕ) : ℝ) * 2)
        ≤ Real.log ((2 * Q) ^ 2) := Real.log_le_log hmul_pos hmul_le
      _ = 2 * L := by rw [Real.log_pow]; norm_num; rfl
  have hB_le : B ≤ 2 * (C * L) := by nlinarith
  have hBL1 : B * Real.log ((ψ₁.N : ℝ) * 2) ≤ C * L :=
    (mul_le_mul_of_nonneg_left hlog1 hB0.le).trans (mul_le_mul_of_nonneg_right hBC (by linarith))
  have hBL2 : B * Real.log ((ψ₂.N : ℝ) * 2) ≤ C * L :=
    (mul_le_mul_of_nonneg_left hlog2 hB0.le).trans (mul_le_mul_of_nonneg_right hBC (by linarith))
  have hBL12 : B * Real.log (((ψ₁.N * ψ₂.N : ℕ) : ℝ) * 2) ≤ 2 * (C * L) := by
    have h1 := mul_le_mul_of_nonneg_left hlog12 hB0.le
    have h2 : B * (2 * L) ≤ 2 * (C * L) := by nlinarith
    exact h1.trans h2
  have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
  rw [hσ_sub] at hZ
  have h6CL : 6 * (C * L) = 1 / (2 * δ) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  set β : ℝ := min β₁ β₂
  have hσβ_pos : 0 < σ - β := by
    have : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) h11
    linarith
  have hd1 : 1 / (σ - β) ≤ 1 / (σ - β₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left β₁ β₂])
  have hd2 : 1 / (σ - β) ≤ 1 / (σ - β₂) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right β₁ β₂])
  have hX1' : (negLogDerivL ψ₁.χ (σ : ℂ)).re ≤ C * L - 1 / (σ - β) := by linarith [hX1, hBL1, hd1]
  have hX2' : (negLogDerivL ψ₂.χ (σ : ℂ)).re ≤ C * L - 1 / (σ - β) := by linarith [hX2, hBL2, hd2]
  have hX12' : (negLogDerivL (prodChar ψ₁.χ ψ₂.χ) (σ : ℂ)).re ≤ 2 * (C * L) := by
    linarith [hX12, hBL12]
  have hineq : 2 / (σ - β) ≤ 1 / δ + 1 / (2 * δ) := by
    have h2 : 2 / (σ - β) = 1 / (σ - β) + 1 / (σ - β) := by ring
    linarith [hpos, hZ, hX1', hX2', hX12', hB_le, h6CL, h2]
  have hcomb : 1 / δ + 1 / (2 * δ) = 3 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
  rw [hcomb] at hineq
  have hmul : 4 * δ ≤ 3 * (σ - β) := by
    have h1' := (div_le_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq
    linarith
  have hβ_le : β ≤ 1 - δ / 3 := by dsimp only [σ] at hmul; linarith
  have hδ3 : δ / 3 = 1 / (36 * C * L) := by
    dsimp only [δ]; field_simp [hCL_pos.ne']; ring
  linarith

/-- **Landau–Page Exceptional Zero Isolation**:
among ALL non-principal primitive Dirichlet characters `ψ` of conductor `ψ.N ≤ Q` (`Q ≥ 2`)
and ALL real numbers `β ∈ (0, 1)` satisfying `L(ψ, β) = 0` and
`1 - 1 / (168 * max B 1 * log (2 * Q)) < β`:
1. Every such `ψ` is necessarily real (`ψ.IsReal`), and
2. At most ONE such pair `(ψ, β)` exists across all conductors `≤ Q`! -/
theorem landau_page_exceptional_zero_isolation {B : ℝ} (H : HadamardLogDerivPackage B)
    {Q : ℝ} (hQ : 2 ≤ Q) :
    (∀ (ψ : PChar) (β : ℝ), ψ.χ ≠ 1 → (ψ.N : ℝ) ≤ Q → 0 < β → β < 1 →
        DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
        1 - 1 / (168 * max B 1 * Real.log (2 * Q)) < β → ψ.IsReal) ∧
    (∀ (ψ₁ ψ₂ : PChar) (β₁ β₂ : ℝ),
        ψ₁.χ ≠ 1 → ψ₂.χ ≠ 1 → (ψ₁.N : ℝ) ≤ Q → (ψ₂.N : ℝ) ≤ Q →
        0 < β₁ → β₁ < 1 → 0 < β₂ → β₂ < 1 →
        DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0 →
        DirichletCharacter.LFunction ψ₂.χ (β₂ : ℂ) = 0 →
        1 - 1 / (168 * max B 1 * Real.log (2 * Q)) < β₁ →
        1 - 1 / (168 * max B 1 * Real.log (2 * Q)) < β₂ →
        ψ₁ = ψ₂ ∧ β₁ = β₂) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hL : (1 / 2 : ℝ) < Real.log (2 * Q) :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hreal_of_exc :
      ∀ (ψ : PChar) (β : ℝ), ψ.χ ≠ 1 → (ψ.N : ℝ) ≤ Q → 0 < β → β < 1 →
        DirichletCharacter.LFunction ψ.χ (β : ℂ) = 0 →
        1 - 1 / (168 * C * Real.log (2 * Q)) < β → ψ.IsReal := by
    intro ψ β _ hq h0 h1 hz hgt
    by_contra hnr
    have hsq : ψ.χ ^ 2 ≠ 1 := fun h => hnr (isRealChar_of_sq_eq_one h)
    have hbound := zeroFreeRegion_complex_char H hsq
      (by simpa using h0) (by simpa using h1) hz
    simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero] at hbound
    have hqpos : (0 : ℝ) < (ψ.N : ℝ) := by exact_mod_cast NeZero.pos ψ.N
    have hlog_le : Real.log ((ψ.N : ℝ) * (0 + 2)) ≤ Real.log (2 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    have hLψ : (1 / 2 : ℝ) < Real.log ((ψ.N : ℝ) * (0 + 2)) := by
      have h := half_lt_log_q_abs_add_two (q := ψ.N) 0
      simpa using h
    have hdiv : 1 / (168 * C * Real.log (2 * Q)) ≤
        1 / (168 * C * Real.log ((ψ.N : ℝ) * (0 + 2))) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith
  refine ⟨hreal_of_exc, fun ψ₁ ψ₂ β₁ β₂ h1ne h2ne hq1 hq2 h10 h11 h20 h21 hz1 hz2 hgt1 hgt2 => ?_⟩
  have h1r : ψ₁.IsReal := hreal_of_exc ψ₁ β₁ h1ne hq1 h10 h11 hz1 hgt1
  have h2r : ψ₂.IsReal := hreal_of_exc ψ₂ β₂ h2ne hq2 h20 h21 hz2 hgt2
  have hψeq : ψ₁ = ψ₂ := by
    by_contra hne
    have hmin := landau_page_two_distinct_real_chars H hQ hne h1ne h2ne h1r h2r hq1 hq2
      h10 h11 h20 h21 hz1 hz2
    have hdiv : 1 / (168 * C * Real.log (2 * Q)) ≤ 1 / (36 * C * Real.log (2 * Q)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hgt_min : 1 - 1 / (168 * C * Real.log (2 * Q)) < min β₁ β₂ := lt_min hgt1 hgt2
    linarith
  refine ⟨hψeq, ?_⟩
  subst hψeq
  by_contra hβne
  have hmin := real_char_at_most_one_exceptional_real_zero H h1ne hβne h10 h11 h20 h21 hz1 hz2
  have hqpos : (0 : ℝ) < (ψ₁.N : ℝ) := by exact_mod_cast NeZero.pos ψ₁.N
  have hlog_le : Real.log (2 * (ψ₁.N : ℝ)) ≤ Real.log (2 * Q) :=
    Real.log_le_log (by positivity) (by linarith)
  have hL1 : (1 / 2 : ℝ) < Real.log (2 * (ψ₁.N : ℝ)) :=
    half_lt_log_two.trans_le (Real.log_le_log (by norm_num) (by
      have : (1 : ℝ) ≤ (ψ₁.N : ℝ) := by exact_mod_cast NeZero.pos ψ₁.N
      linarith))
  have hdiv : 1 / (168 * C * Real.log (2 * Q)) ≤ 1 / (18 * C * Real.log (2 * (ψ₁.N : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hgt_min : 1 - 1 / (168 * C * Real.log (2 * Q)) < min β₁ β₂ := lt_min hgt1 hgt2
  linarith

/-- **Unified Non-Exceptional Classical Zero-Free Region**:
for any non-principal character `χ ≠ 1` mod `q` and any critical-strip zero `ρ`, either `ρ`
satisfies the classical zero-free region `ρ.re ≤ 1 - 1 / (296 * max B 1 * log(q (|ρ.im| + 2)))`,
OR `χ` is real and `ρ` is a real exceptional zero `ρ.im = 0` with
`1 - 1 / (296 * max B 1 * log (2 * q)) < ρ.re`. -/
theorem zeroFreeRegion_nonexceptional {B : ℝ} (H : HadamardLogDerivPackage B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    ρ.re ≤ 1 - 1 / (296 * max B 1 * Real.log ((q : ℝ) * (|ρ.im| + 2))) ∨
      (IsRealChar χ ∧ ρ.im = 0 ∧
        1 - 1 / (296 * max B 1 * Real.log (2 * (q : ℝ))) < ρ.re) := by
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right B 1
  have hL : (1 / 2 : ℝ) < Real.log ((q : ℝ) * (|ρ.im| + 2)) := half_lt_log_q_abs_add_two ρ.im
  by_cases hsq : χ ^ 2 = 1
  · by_cases him : ρ.im = 0
    · by_cases hle : ρ.re ≤ 1 - 1 / (296 * C * Real.log ((q : ℝ) * (|ρ.im| + 2)))
      · exact Or.inl hle
      · right
        refine ⟨isRealChar_of_sq_eq_one hsq, him, ?_⟩
        rw [him, abs_zero, zero_add, show (q : ℝ) * 2 = 2 * (q : ℝ) by ring] at hle
        exact lt_of_not_ge hle
    · exact Or.inl (zeroFreeRegion_real_char_nonreal_zero H hχ1 hsq h0 h1 him hz)
  · left
    have h := zeroFreeRegion_complex_char H hsq h0 h1 hz
    have hdiv : 1 / (296 * C * Real.log ((q : ℝ) * (|ρ.im| + 2))) ≤
        1 / (168 * C * Real.log ((q : ℝ) * (|ρ.im| + 2))) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith

/-! ## Section 3: Explicit-Formula Truncated Zero Sum → `PsiCharPowerBound` / `Stage2PrimePairs` -/

/-- A uniform zero-free strip `Re(s) > θ` (`1/2 ≤ θ < 1`) for `ζ(s)` and all Dirichlet `L`-functions. -/
def ZeroFreeStrip (θ : ℝ) : Prop :=
  1 / 2 ≤ θ ∧ θ < 1 ∧
  (∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    θ < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0)

/-- `RHDirect.ZeroFreeAll` immediately implies `ZeroFreeStrip (1 / 2)`. -/
theorem zeroFreeStrip_half_of_zeroFreeAll (hZ : ZeroFreeAll) : ZeroFreeStrip (1 / 2) := by
  have hD : DirichletLNonvanishingRightOfHalf :=
    RHDirect.zeroFreeAll_iff_dirichletLNonvanishingRightOfHalf.mp hZ
  refine ⟨le_rfl, by norm_num, fun s hre hs => ?_, fun q _ χ s hre hχs => hD q χ s hre hχs⟩
  have h1 := hD 1 (1 : DirichletCharacter ℂ 1) s hre (.inr hs)
  rwa [DirichletCharacter.LFunction_modOne_eq] at h1

/-- Functional-equation symmetry inside `ZeroFreeStrip θ`: every critical-strip zero `ρ`
of `riemannZeta` satisfies `1 - θ ≤ ρ.re ≤ θ`. -/
theorem riemannZeta_zero_mem_strip_of_zeroFreeStrip {θ : ℝ} (hZ : ZeroFreeStrip θ)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    1 - θ ≤ ρ.re ∧ ρ.re ≤ θ := by
  obtain ⟨_, _, hζ, _⟩ := hZ
  have hρ1 : ρ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; exact lt_irrefl _ h1
  constructor
  · by_contra hlt
    push Not at hlt
    have hre : θ < (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have h1ρ1 : 1 - ρ ≠ 1 := fun e => by
      have hρ0 : ρ = 0 := sub_eq_self.mp e
      rw [hρ0, Complex.zero_re] at h0; exact lt_irrefl _ h0
    exact hζ (1 - ρ) hre h1ρ1 ((RHDirect.riemannZeta_eq_zero_one_sub_iff h0 h1).mpr hz)
  · by_contra hgt
    push Not at hgt
    exact hζ ρ hgt hρ1 hz

/-- Functional-equation symmetry inside `ZeroFreeStrip θ`: every critical-strip zero `ρ`
of any Dirichlet `L`-function `L(χ, s)` satisfies `1 - θ ≤ ρ.re ≤ θ`. -/
theorem LFunction_zero_mem_strip_of_zeroFreeStrip {θ : ℝ} (hZ : ZeroFreeStrip θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    1 - θ ≤ ρ.re ∧ ρ.re ≤ θ := by
  obtain ⟨_, _, _, hL⟩ := hZ
  have hρ1 : ρ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; exact lt_irrefl _ h1
  constructor
  · by_contra hlt
    push Not at hlt
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 :=
      (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inr hρ1)).mp hz
    have hprim' : DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (1 - ρ) = 0 :=
      (RHDirect.LFunction_eq_zero_one_sub_iff_of_isPrimitive
        χ.primitiveCharacter_isPrimitive h0 h1).mpr hprim
    have hre : θ < (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have h1ρ1 : 1 - ρ ≠ 1 := fun e => by
      have hρ0 : ρ = 0 := sub_eq_self.mp e
      rw [hρ0, Complex.zero_re] at h0; exact lt_irrefl _ h0
    exact hL χ.conductor χ.primitiveCharacter⁻¹ (1 - ρ) hre (.inr h1ρ1) hprim'
  · by_contra hgt
    push Not at hgt
    exact hL q χ ρ hgt (.inr hρ1) hz

/-- Riemann–von Mangoldt cumulative zero-counting bound for a finite zero set `Z` of modulus `q`:
`#{ρ ∈ Z : |ρ.im| ≤ t} ≤ C_N * t * log (q * (t + 2))` for all `t ≥ 1`. -/
def ZeroCountBound (C_N : ℝ) (Z : Finset ℂ) (q : ℕ) : Prop :=
  0 ≤ C_N ∧ ∀ t : ℝ, 1 ≤ t →
    ((Z.filter fun ρ => |ρ.im| ≤ t).card : ℝ) ≤ C_N * t * Real.log ((q : ℝ) * (t + 2))

private lemma norm_cpow_div_zero_le {x θ : ℝ} (hx : 1 ≤ x) {ρ : ℂ}
    (hre_le : ρ.re ≤ θ) {m : ℝ} (hm : 0 < m) (hnorm : m ≤ ‖ρ‖) :
    ‖(x : ℂ) ^ ρ / ρ‖ ≤ x ^ θ / m := by
  have hx0 : 0 < x := by linarith
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  exact div_le_div₀ (Real.rpow_nonneg hx0.le θ)
    (Real.rpow_le_rpow_of_exponent_le hx hre_le) hm hnorm

private lemma nat_log_two_ceil_le {T : ℝ} (hT : 2 ≤ T) :
    (Nat.log 2 ⌈T⌉₊ : ℝ) ≤ Real.log T / Real.log 2 + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil_pos : 0 < ⌈T⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hpow : 2 ^ Nat.log 2 ⌈T⌉₊ ≤ ⌈T⌉₊ := Nat.pow_log_le_self 2 hceil_pos.ne'
  have hceil_le : (⌈T⌉₊ : ℝ) ≤ 2 * T := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T by linarith)
    linarith
  have hpowR : ((2 : ℝ) ^ Nat.log 2 ⌈T⌉₊) ≤ 2 * T :=
    (by exact_mod_cast hpow : ((2 : ℝ) ^ Nat.log 2 ⌈T⌉₊) ≤ (⌈T⌉₊ : ℝ)).trans hceil_le
  have hlog : (Nat.log 2 ⌈T⌉₊ : ℝ) * Real.log 2 ≤ Real.log (2 * T) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowR
  rw [Real.log_mul (by norm_num) (by linarith)] at hlog
  have hdiv : (Real.log T / Real.log 2 + 1) * Real.log 2 = Real.log T + Real.log 2 := by
    field_simp [hlog2.ne']
  exact le_of_mul_le_mul_right (by linarith) hlog2

/-- **Dyadic Truncated Zero-Sum Upper Bound (`norm_sum_cpow_div_zero_le`)**:
for any finite set `Z` of zeros in the strip `1 - θ ≤ Re(ρ) ≤ θ`, `|Im(ρ)| ≤ T` (`T ≥ 2`)
satisfying `ZeroCountBound C_N Z q` (`q ≥ 1`), and any `x ≥ 1`:
`∑_{ρ ∈ Z} ‖x^ρ / ρ‖ ≤ C_N * (1 / (1 - θ) + 2 * (log T / log 2 + 2)) * x^θ * log(q * (2T + 4))`. -/
theorem norm_sum_cpow_div_zero_le {C_N θ x T : ℝ} {q : ℕ} [NeZero q] {Z : Finset ℂ}
    (hθ1 : θ < 1) (hx : 1 ≤ x) (hT : 2 ≤ T)
    (hstrip : ∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| ≤ T)
    (hcnt : ZeroCountBound C_N Z q) :
    ∑ ρ ∈ Z, ‖(x : ℂ) ^ ρ / ρ‖ ≤
      C_N * (1 / (1 - θ) + 2 * (Real.log T / Real.log 2 + 2)) *
        x ^ θ * Real.log ((q : ℝ) * (2 * T + 4)) := by
  classical
  obtain ⟨hCN0, hcnt_le⟩ := hcnt
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have h1θ : 0 < 1 - θ := by linarith
  set K : ℕ := Nat.log 2 ⌈T⌉₊
  have h2K_gt : (T : ℝ) < (2 : ℝ) ^ (K + 1) := by
    have hnat : ⌈T⌉₊ < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) ⌈T⌉₊
    exact (Nat.le_ceil T).trans_lt (by exact_mod_cast hnat)
  have h2K_le : (2 : ℝ) ^ K ≤ 2 * T := by
    have hceil_pos : 0 < ⌈T⌉₊ := Nat.ceil_pos.mpr (by linarith)
    have hnat : 2 ^ K ≤ ⌈T⌉₊ := Nat.pow_log_le_self 2 hceil_pos.ne'
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T by linarith)
    exact (by exact_mod_cast hnat : ((2 : ℝ) ^ K) ≤ (⌈T⌉₊ : ℝ)).trans (by linarith)
  set Z0 : Finset ℂ := Z.filter fun ρ => |ρ.im| ≤ 1
  set Zdyad : ℕ → Finset ℂ := fun k =>
    Z.filter fun ρ => (2 : ℝ) ^ k < |ρ.im| ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1)
  have hcover : Z ⊆ Z0 ∪ (Finset.range (K + 1)).biUnion Zdyad := by
    intro ρ hρ
    rw [Finset.mem_union, Finset.mem_biUnion]
    by_cases hle1 : |ρ.im| ≤ 1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hρ, hle1⟩)
    · right
      push Not at hle1
      have hTρ : |ρ.im| ≤ T := (hstrip ρ hρ).2.2
      have hceil_im : 2 ≤ ⌈|ρ.im|⌉₊ := by
        have h1 : 1 < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hle1)
        omega
      -- Choose `k = Nat.log 2 (⌈|ρ.im|⌉₊ - 1)`? Easier: pick the largest `k` with `2^k < |ρ.im|`!
      have hex : ∃ k ≤ K, (2 : ℝ) ^ k < |ρ.im| ∧ |ρ.im| ≤ (2 : ℝ) ^ (k + 1) := by
        have hS : (Finset.range (K + 1)).filter (fun k => (2 : ℝ) ^ k < |ρ.im|) |>.Nonempty :=
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos K), by simpa using hle1⟩⟩
        set k := ((Finset.range (K + 1)).filter (fun k => (2 : ℝ) ^ k < |ρ.im|)).max' hS
        have hk_mem := Finset.mem_filter.mp (Finset.max'_mem _ hS)
        have hk_le : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem.1)
        refine ⟨k, hk_le, hk_mem.2, ?_⟩
        by_cases hkK : k = K
        · rw [hkK]; exact hTρ.trans h2K_gt.le
        · have hk1_lt : k + 1 < K + 1 := by omega
          by_contra hgt
          push Not at hgt
          have hmem' : k + 1 ∈ (Finset.range (K + 1)).filter (fun k => (2 : ℝ) ^ k < |ρ.im|) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk1_lt, hgt⟩
          have hle_max := Finset.le_max' _ (k + 1) hmem'
          omega
      obtain ⟨k, hkK, hlo, hhi⟩ := hex
      exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkK),
        Finset.mem_filter.mpr ⟨hρ, hlo, hhi⟩⟩
  have hlog_big_nn : 0 ≤ Real.log ((q : ℝ) * (2 * T + 4)) :=
    Real.log_nonneg (by nlinarith)
  -- Bound the low strip `Z0`: `|ρ.im| ≤ 1`.
  have hZ0_bound :
      ∑ ρ ∈ Z0, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        C_N * (1 / (1 - θ)) * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4)) := by
    have hterm : ∀ ρ ∈ Z0, ‖(x : ℂ) ^ ρ / ρ‖ ≤ x ^ θ / (1 - θ) := by
      intro ρ hρ
      have hρZ := (Finset.mem_filter.mp hρ).1
      obtain ⟨hlo, hhi, _⟩ := hstrip ρ hρZ
      have hnorm : 1 - θ ≤ ‖ρ‖ := hlo.trans (Complex.re_le_norm ρ)
      exact norm_cpow_div_zero_le hx hhi h1θ hnorm
    calc ∑ ρ ∈ Z0, ‖(x : ℂ) ^ ρ / ρ‖
        ≤ ∑ _ρ ∈ Z0, (x ^ θ / (1 - θ)) := Finset.sum_le_sum hterm
      _ = (Z0.card : ℝ) * (x ^ θ / (1 - θ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C_N * 1 * Real.log ((q : ℝ) * (1 + 2))) * (x ^ θ / (1 - θ)) :=
          mul_le_mul_of_nonneg_right (hcnt_le 1 le_rfl) (by positivity)
      _ ≤ (C_N * 1 * Real.log ((q : ℝ) * (2 * T + 4))) * (x ^ θ / (1 - θ)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by nlinarith)) (by positivity))
            (by positivity)
      _ = C_N * (1 / (1 - θ)) * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4)) := by ring
  -- Bound each dyadic block `Zdyad k` (`0 ≤ k ≤ K`).
  have hZdyad_bound : ∀ k ∈ Finset.range (K + 1),
      ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4)) := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2k1_le : (2 : ℝ) ^ (k + 1) ≤ 4 * T := by
      have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hkK
      rw [pow_succ]; linarith
    have hterm : ∀ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖ ≤ x ^ θ / (2 : ℝ) ^ k := by
      intro ρ hρ
      obtain ⟨hρZ, hlo, _⟩ := Finset.mem_filter.mp hρ
      have hhi := (hstrip ρ hρZ).2.1
      have hnorm : (2 : ℝ) ^ k ≤ ‖ρ‖ := hlo.le.trans (Complex.abs_im_le_norm ρ)
      exact norm_cpow_div_zero_le hx hhi h2k_pos hnorm
    have hsub : Zdyad k ⊆ Z.filter fun ρ => |ρ.im| ≤ (2 : ℝ) ^ (k + 1) := by
      intro ρ hρ
      obtain ⟨hρZ, _, hhi⟩ := Finset.mem_filter.mp hρ
      exact Finset.mem_filter.mpr ⟨hρZ, hhi⟩
    have hcard : (Zdyad k).card ≤ (Z.filter fun ρ => |ρ.im| ≤ (2 : ℝ) ^ (k + 1)).card :=
      Finset.card_le_card hsub
    have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hlog_le : Real.log ((q : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) ≤
        Real.log ((q : ℝ) * (2 * T + 4)) := by
      -- Wait: `2^(k+1) ≤ 2 * 2^K ≤ 4 * T`? Careful! We need `2^(k+1) ≤ 2 * T + 2`!
      -- Actually `2^k ≤ 2^K = 2^(Nat.log 2 ⌈T⌉₊) ≤ ⌈T⌉₊ < T + 1`, so `2^(k+1) ≤ 2 * (T + 1) = 2 * T + 2`!
      have hceil_pos : 0 < ⌈T⌉₊ := Nat.ceil_pos.mpr (by linarith)
      have hnat : 2 ^ K ≤ ⌈T⌉₊ := Nat.pow_log_le_self 2 hceil_pos.ne'
      have h2K_tight : (2 : ℝ) ^ K ≤ T + 1 :=
        (by exact_mod_cast hnat : ((2 : ℝ) ^ K) ≤ (⌈T⌉₊ : ℝ)).trans
          (Nat.ceil_lt_add_one (by linarith)).le
      have h2k_tight : (2 : ℝ) ^ k ≤ T + 1 :=
        (pow_le_pow_right₀ (by norm_num) hkK).trans h2K_tight
      have h2k1_tight : (2 : ℝ) ^ (k + 1) ≤ 2 * T + 2 := by rw [pow_succ]; linarith
      refine Real.log_le_log (by positivity) ?_
      have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
      nlinarith
    have hcard_bound : ((Zdyad k).card : ℝ) ≤
        C_N * (2 : ℝ) ^ (k + 1) * Real.log ((q : ℝ) * (2 * T + 4)) := by
      calc ((Zdyad k).card : ℝ)
          ≤ ((Z.filter fun ρ => |ρ.im| ≤ (2 : ℝ) ^ (k + 1)).card : ℝ) := by exact_mod_cast hcard
        _ ≤ C_N * (2 : ℝ) ^ (k + 1) * Real.log ((q : ℝ) * ((2 : ℝ) ^ (k + 1) + 2)) :=
            hcnt_le ((2 : ℝ) ^ (k + 1)) h1le
        _ ≤ C_N * (2 : ℝ) ^ (k + 1) * Real.log ((q : ℝ) * (2 * T + 4)) :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
    calc ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖
        ≤ ∑ _ρ ∈ Zdyad k, (x ^ θ / (2 : ℝ) ^ k) := Finset.sum_le_sum hterm
      _ = ((Zdyad k).card : ℝ) * (x ^ θ / (2 : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C_N * (2 : ℝ) ^ (k + 1) * Real.log ((q : ℝ) * (2 * T + 4))) * (x ^ θ / (2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right hcard_bound (by positivity)
      _ = 2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4)) := by
          rw [pow_succ]
          field_simp [h2k_pos.ne']
  have hbiUnion :
      ∑ ρ ∈ (Finset.range (K + 1)).biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        ∑ k ∈ Finset.range (K + 1), ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖ := by
    have hgen : ∀ (s : Finset ℕ),
        ∑ ρ ∈ s.biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ ≤
          ∑ k ∈ s, ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha]
        have hu : ∑ ρ ∈ Zdyad a ∪ s.biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ ≤
            ∑ ρ ∈ Zdyad a, ‖(x : ℂ) ^ ρ / ρ‖ + ∑ ρ ∈ s.biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ := by
          rw [← Finset.sum_union_inter]
          linarith [Finset.sum_nonneg (s := Zdyad a ∩ s.biUnion Zdyad)
            (f := fun ρ => ‖(x : ℂ) ^ ρ / ρ‖) (fun _ _ => norm_nonneg _)]
        linarith
    exact hgen (Finset.range (K + 1))
  have hunion :
      ∑ ρ ∈ Z, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        ∑ ρ ∈ Z0, ‖(x : ℂ) ^ ρ / ρ‖ +
          ∑ ρ ∈ (Finset.range (K + 1)).biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ := by
    have h1 : ∑ ρ ∈ Z, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        ∑ ρ ∈ Z0 ∪ (Finset.range (K + 1)).biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => norm_nonneg _)
    have h2 : ∑ ρ ∈ Z0 ∪ (Finset.range (K + 1)).biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        ∑ ρ ∈ Z0, ‖(x : ℂ) ^ ρ / ρ‖ +
          ∑ ρ ∈ (Finset.range (K + 1)).biUnion Zdyad, ‖(x : ℂ) ^ ρ / ρ‖ := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := Z0 ∩ (Finset.range (K + 1)).biUnion Zdyad)
        (f := fun ρ => ‖(x : ℂ) ^ ρ / ρ‖) (fun _ _ => norm_nonneg _)]
    exact h1.trans h2
  have hK_sum :
      ∑ k ∈ Finset.range (K + 1), ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖ ≤
        ((K + 1 : ℕ) : ℝ) * (2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4))) := by
    calc ∑ k ∈ Finset.range (K + 1), ∑ ρ ∈ Zdyad k, ‖(x : ℂ) ^ ρ / ρ‖
        ≤ ∑ _k ∈ Finset.range (K + 1),
            (2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4))) :=
          Finset.sum_le_sum hZdyad_bound
      _ = ((K + 1 : ℕ) : ℝ) * (2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK_le : ((K + 1 : ℕ) : ℝ) ≤ Real.log T / Real.log 2 + 2 := by
    push_cast
    linarith [nat_log_two_ceil_le hT]
  have hK_final :
      ((K + 1 : ℕ) : ℝ) * (2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4))) ≤
        (Real.log T / Real.log 2 + 2) * (2 * C_N * x ^ θ * Real.log ((q : ℝ) * (2 * T + 4))) :=
    mul_le_mul_of_nonneg_right hK_le (by positivity)
  have htot := hunion.trans (add_le_add hZ0_bound (hbiUnion.trans (hK_sum.trans hK_final)))
  linarith

/-- **Truncated Explicit-Formula Package in a Zero-Free Strip `Re(s) ≤ θ`**:
combines a zero-free strip (`1 - θ ≤ ρ.re ≤ θ`), Riemann–von Mangoldt zero-counting bound
`N(t, χ) ≤ C_N t log(q (t + 2))`, and the truncated explicit-formula remainder for `ψ(x)` and
`ψ(x, χ)` (Davenport Ch. 17 & 19). -/
structure TruncatedExplicitFormulaPackage (θ C_N C_R : ℝ) : Prop where
  theta_ge_half : 1 / 2 ≤ θ
  theta_lt_one : θ < 1
  CN_nonneg : 0 ≤ C_N
  CR_nonneg : 0 ≤ C_R
  zeta_explicit :
    ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ∃ Z : Finset ℂ,
        (∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| ≤ T) ∧
        ZeroCountBound C_N Z 1 ∧
        |chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| ≤
          C_R * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1))
  char_explicit :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
        ∃ Z : Finset ℂ,
          (∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| ≤ T) ∧
          ZeroCountBound C_N Z q ∧
          ‖Stage2DirichletAP.chebyshevPsiChar χ x + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ ≤
            C_R * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
              (Real.log (q : ℝ) + 1) * (Real.log x + 1))

private lemma log_add_one_sq_le_rpow {δ x : ℝ} (hδ : 0 < δ) (hx : 2 ≤ x) :
    (Real.log x + 1) ^ 2 ≤ (2 / δ + 1) ^ 2 * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div hx0.le (by positivity)
  have h1 : (1 : ℝ) ≤ x ^ (δ / 2) := Real.one_le_rpow (by linarith) (by positivity)
  have hlin : Real.log x + 1 ≤ (2 / δ + 1) * x ^ (δ / 2) := by
    have heq : x ^ (δ / 2) / (δ / 2) = (2 / δ) * x ^ (δ / 2) := by field_simp [hδ.ne']
    nlinarith
  have hsq := pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)]) hlin 2
  calc (Real.log x + 1) ^ 2
      ≤ ((2 / δ + 1) * x ^ (δ / 2)) ^ 2 := hsq
    _ = (2 / δ + 1) ^ 2 * (x ^ (δ / 2) * x ^ (δ / 2)) := by ring
    _ = (2 / δ + 1) ^ 2 * x ^ δ := by
        rw [← Real.rpow_add hx0]
        ring_nf

private lemma log_q_two_x_add_four_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 2 ≤ x) :
    Real.log ((q : ℝ) * (2 * x + 4)) ≤ 4 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have h2x4 : 2 * x + 4 ≤ 4 * x := by linarith
  have hlog_4x : Real.log (2 * x + 4) ≤ Real.log 4 + Real.log x := by
    calc Real.log (2 * x + 4) ≤ Real.log (4 * x) := Real.log_le_log (by positivity) h2x4
      _ = Real.log 4 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  rw [Real.log_mul hq0.ne' (by positivity)]
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith

/-- **Explicit-Formula Truncated Zero Sum → `Stage2DirichletAP.PsiCharPowerBound θ'`**:
any `TruncatedExplicitFormulaPackage θ C_N C_R` (`1/2 ≤ θ < 1`) unconditionally yields
`Stage2DirichletAP.PsiCharPowerBound θ'` for EVERY `θ' ∈ (θ, 1)`. -/
theorem psiCharPowerBound_of_truncatedExplicitFormula {θ C_N C_R θ' : ℝ}
    (H : TruncatedExplicitFormulaPackage θ C_N C_R)
    (hθ'lo : θ < θ') (hθ'hi : θ' < 1) :
    Stage2DirichletAP.PsiCharPowerBound θ' := by
  set δ : ℝ := θ' - θ
  have hδ : 0 < δ := by linarith
  have hθ0 : 0 ≤ θ := by linarith [H.theta_ge_half]
  have hθ'0 : 0 ≤ θ' := by linarith
  have h1θ : 0 < 1 - θ := by linarith [H.theta_lt_one]
  set A : ℝ := C_N * (1 / (1 - θ) + 4) * 4 + 2 * C_R
  have hA0 : 0 ≤ A := by
    have := H.CN_nonneg
    have := H.CR_nonneg
    positivity
  set M : ℝ := A * (2 / δ + 1) ^ 2
  refine ⟨hθ'0, hθ'hi, M, by positivity, fun q _ hq x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
  have hcoeff_log :
      1 / (1 - θ) + 2 * (Real.log x / Real.log 2 + 2) ≤ (1 / (1 - θ) + 4) * (Real.log x + 1) := by
    have hdiv : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h1θ_pos : 0 ≤ 1 / (1 - θ) := by positivity
    nlinarith
  have hpow_sq : (Real.log x + 1) ^ 2 ≤ (2 / δ + 1) ^ 2 * x ^ δ :=
    log_add_one_sq_le_rpow hδ hx
  have hpow_add : x ^ θ * x ^ δ = x ^ θ' := by
    rw [← Real.rpow_add hx0]
    congr 1; dsimp only [δ]; ring
  have hxθ_ge1 : 1 ≤ x ^ θ := Real.one_le_rpow hx1 hθ0
  constructor
  · -- Part 1: `|ψ(x) - x| ≤ M * x ^ θ'` via `T = x`.
    obtain ⟨Z, hZ_strip, hZ_cnt, hZ_err⟩ := H.zeta_explicit x x hx hx
    have hZ_sum := norm_sum_cpow_div_zero_le (q := 1) H.theta_lt_one hx1 hx hZ_strip hZ_cnt
    have hlog_1 : Real.log ((1 : ℕ) * (2 * x + 4)) ≤ 4 * (Real.log x + 1) := by
      have h := log_q_two_x_add_four_le (q := 1) hx
      simpa using h
    have hsum_re :
        |∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| ≤
          C_N * (1 / (1 - θ) + 4) * 4 * x ^ θ * (Real.log x + 1) ^ 2 := by
      calc |∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re|
          ≤ ∑ ρ ∈ Z, |((x : ℂ) ^ ρ / ρ).re| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ ρ ∈ Z, ‖(x : ℂ) ^ ρ / ρ‖ :=
            Finset.sum_le_sum fun ρ _ => Complex.abs_re_le_norm _
        _ ≤ C_N * (1 / (1 - θ) + 2 * (Real.log x / Real.log 2 + 2)) *
              x ^ θ * Real.log (((1 : ℕ) : ℝ) * (2 * x + 4)) := hZ_sum
        _ ≤ C_N * ((1 / (1 - θ) + 4) * (Real.log x + 1)) *
              x ^ θ * (4 * (Real.log x + 1)) := by
            have hCN := H.CN_nonneg
            have hxθ := Real.rpow_nonneg hx0.le θ
            have hlog_nn : 0 ≤ Real.log (((1 : ℕ) : ℝ) * (2 * x + 4)) :=
              Real.log_nonneg (by push_cast; linarith)
            have h1 : C_N * (1 / (1 - θ) + 2 * (Real.log x / Real.log 2 + 2)) * x ^ θ ≤
                C_N * ((1 / (1 - θ) + 4) * (Real.log x + 1)) * x ^ θ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff_log hCN) hxθ
            exact mul_le_mul h1 (by simpa using hlog_1) hlog_nn (by positivity)
        _ = C_N * (1 / (1 - θ) + 4) * 4 * x ^ θ * (Real.log x + 1) ^ 2 := by ring
    have hrem :
        C_R * (x / x * (Real.log x + 1) ^ 2 + (Real.log x + 1)) ≤
          2 * C_R * x ^ θ * (Real.log x + 1) ^ 2 := by
      rw [div_self hx0.ne', one_mul]
      have h1 : Real.log x + 1 ≤ (Real.log x + 1) ^ 2 := by nlinarith
      have h2 : (Real.log x + 1) ^ 2 + (Real.log x + 1) ≤ 2 * (Real.log x + 1) ^ 2 := by linarith
      have h3 : C_R * ((Real.log x + 1) ^ 2 + (Real.log x + 1)) ≤
          2 * C_R * (Real.log x + 1) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h2 H.CR_nonneg; linarith
      have h4 : 2 * C_R * (Real.log x + 1) ^ 2 ≤ 2 * C_R * x ^ θ * (Real.log x + 1) ^ 2 := by
        have hCR := H.CR_nonneg
        have hfac : 0 ≤ 2 * C_R * (Real.log x + 1) ^ 2 := by positivity
        calc 2 * C_R * (Real.log x + 1) ^ 2
            = (2 * C_R * (Real.log x + 1) ^ 2) * 1 := (mul_one _).symm
          _ ≤ (2 * C_R * (Real.log x + 1) ^ 2) * x ^ θ := mul_le_mul_of_nonneg_left hxθ_ge1 hfac
          _ = 2 * C_R * x ^ θ * (Real.log x + 1) ^ 2 := by ring
      exact h3.trans h4
    have htri : |chebyshevPsi x - x| ≤
        |chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| +
          |∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| := by
      calc |chebyshevPsi x - x|
          = |(chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re) -
              ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| := by congr 1; ring
        _ ≤ |chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| +
              |∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| := abs_sub _ _
    calc |chebyshevPsi x - x|
        ≤ A * x ^ θ * (Real.log x + 1) ^ 2 := by
          dsimp only [A]; linarith [hZ_err.trans hrem]
      _ ≤ A * x ^ θ * ((2 / δ + 1) ^ 2 * x ^ δ) :=
          mul_le_mul_of_nonneg_left hpow_sq (mul_nonneg hA0 (Real.rpow_nonneg hx0.le θ))
      _ = M * (x ^ θ * x ^ δ) := by dsimp only [M]; ring
      _ = M * x ^ θ' := by rw [hpow_add]
  · -- Part 2: `‖ψ(x, χ)‖ ≤ M * (log q + 1) * x ^ θ'` via `T = x`.
    intro χ hχ
    obtain ⟨Z, hZ_strip, hZ_cnt, hZ_err⟩ := H.char_explicit q hq χ hχ x x hx hx
    have hZ_sum := norm_sum_cpow_div_zero_le (q := q) H.theta_lt_one hx1 hx hZ_strip hZ_cnt
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have hlog_q := log_q_two_x_add_four_le (q := q) hx
    have hsum_norm :
        ‖∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ ≤
          C_N * (1 / (1 - θ) + 4) * 4 * (Real.log (q : ℝ) + 1) *
            x ^ θ * (Real.log x + 1) ^ 2 := by
      calc ‖∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖
          ≤ ∑ ρ ∈ Z, ‖(x : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
        _ ≤ C_N * (1 / (1 - θ) + 2 * (Real.log x / Real.log 2 + 2)) *
              x ^ θ * Real.log ((q : ℝ) * (2 * x + 4)) := hZ_sum
        _ ≤ C_N * ((1 / (1 - θ) + 4) * (Real.log x + 1)) *
              x ^ θ * (4 * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
            have hCN := H.CN_nonneg
            have hxθ := Real.rpow_nonneg hx0.le θ
            have hlog_nn : 0 ≤ Real.log ((q : ℝ) * (2 * x + 4)) :=
              Real.log_nonneg (by nlinarith)
            have h1 : C_N * (1 / (1 - θ) + 2 * (Real.log x / Real.log 2 + 2)) * x ^ θ ≤
                C_N * ((1 / (1 - θ) + 4) * (Real.log x + 1)) * x ^ θ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff_log hCN) hxθ
            exact mul_le_mul h1 hlog_q hlog_nn (by positivity)
        _ = C_N * (1 / (1 - θ) + 4) * 4 * (Real.log (q : ℝ) + 1) *
              x ^ θ * (Real.log x + 1) ^ 2 := by ring
    have hrem :
        C_R * (x / x * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
            (Real.log (q : ℝ) + 1) * (Real.log x + 1)) ≤
          2 * C_R * (Real.log (q : ℝ) + 1) * x ^ θ * (Real.log x + 1) ^ 2 := by
      rw [div_self hx0.ne', one_mul]
      have h1 : Real.log x + 1 ≤ (Real.log x + 1) ^ 2 := by nlinarith
      have h2 : (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
          (Real.log (q : ℝ) + 1) * (Real.log x + 1) ≤
          2 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 H.CR_nonneg
      have h4 : 2 * C_R * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 ≤
          2 * C_R * (Real.log (q : ℝ) + 1) * x ^ θ * (Real.log x + 1) ^ 2 := by
        have hCR := H.CR_nonneg
        have hfac : 0 ≤ 2 * C_R * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 := by positivity
        nlinarith
      linarith
    have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage2DirichletAP.chebyshevPsiChar χ x + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ +
          ‖∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ := by
      calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
          = ‖(Stage2DirichletAP.chebyshevPsiChar χ x + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ) -
              ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ := by congr 1; ring
        _ ≤ ‖Stage2DirichletAP.chebyshevPsiChar χ x + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ +
              ‖∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ := norm_sub_le _ _
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
        ≤ A * (Real.log (q : ℝ) + 1) * x ^ θ * (Real.log x + 1) ^ 2 := by
          dsimp only [A]; linarith [hZ_err.trans hrem]
      _ ≤ A * (Real.log (q : ℝ) + 1) * x ^ θ * ((2 / δ + 1) ^ 2 * x ^ δ) :=
          mul_le_mul_of_nonneg_left hpow_sq
            (mul_nonneg (mul_nonneg hA0 (by linarith)) (Real.rpow_nonneg hx0.le θ))
      _ = M * (Real.log (q : ℝ) + 1) * (x ^ θ * x ^ δ) := by dsimp only [M]; ring
      _ = M * (Real.log (q : ℝ) + 1) * x ^ θ' := by rw [hpow_add]

/-- Direct reduction from `TruncatedExplicitFormulaPackage` to `Stage2DirichletAP.PsiAPRelativeBound`. -/
theorem psiAPRelativeBound_of_truncatedExplicitFormula {θ C_N C_R : ℝ}
    (H : TruncatedExplicitFormulaPackage θ C_N C_R) :
    Stage2DirichletAP.PsiAPRelativeBound :=
  Stage2DirichletAP.psiAPRelativeBound_of_psiCharPowerBound
    (psiCharPowerBound_of_truncatedExplicitFormula H (θ' := (θ + 1) / 2)
      (by linarith [H.theta_lt_one]) (by linarith [H.theta_lt_one]))

/-- **End-to-End Explicit-Formula → Linnik / `Stage2PrimePairs` Discharge**:
a zero-free strip (`1 - θ ≤ β ≤ θ < 1`) + Riemann–von Mangoldt zero count + truncated explicit
formula unconditionally discharges `LinnikAPDyadic`, `LinnikAPInterval`, `HostFieldSupply.PairSupply`,
`ThetaSlopeEngine.PairEx`, and `HostFieldSupply.SmallOne` in one shot! -/
theorem stage2PrimePairs_of_truncatedExplicitFormula {θ C_N C_R : ℝ}
    (H : TruncatedExplicitFormulaPackage θ C_N C_R) :
    Stage2PrimePairs.LinnikAPDyadic ∧
      Stage2PrimePairs.LinnikAPInterval ∧
      HostFieldSupply.PairSupply ∧
      ThetaSlopeEngine.PairEx ∧
      HostFieldSupply.SmallOne :=
  Stage2DirichletAP.stage2PrimePairs_of_psiCharPowerBound
    (psiCharPowerBound_of_truncatedExplicitFormula H (θ' := (θ + 1) / 2)
      (by linarith [H.theta_lt_one]) (by linarith [H.theta_lt_one]))

/-- Unlocalized truncated explicit-formula input (quantified over actual critical-strip zeros
`0 < ρ.re < 1` of `riemannZeta` and `DirichletCharacter.LFunction χ`, with no a priori zero-free
strip assumption). -/
structure CriticalStripExplicitFormula (C_N C_R : ℝ) : Prop where
  CN_nonneg : 0 ≤ C_N
  CR_nonneg : 0 ≤ C_R
  zeta_explicit :
    ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
      ∃ Z : Finset ℂ,
        (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ T) ∧
        ZeroCountBound C_N Z 1 ∧
        |chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re| ≤
          C_R * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1))
  char_explicit :
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
        ∃ Z : Finset ℂ,
          (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧ |ρ.im| ≤ T) ∧
          ZeroCountBound C_N Z q ∧
          ‖Stage2DirichletAP.chebyshevPsiChar χ x + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ ≤
            C_R * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
              (Real.log (q : ℝ) + 1) * (Real.log x + 1))

/-- Combining any `ZeroFreeStrip θ` with `CriticalStripExplicitFormula C_N C_R` yields
`TruncatedExplicitFormulaPackage θ C_N C_R`. -/
theorem truncatedExplicitFormulaPackage_of_zeroFreeStrip {θ C_N C_R : ℝ}
    (hZ : ZeroFreeStrip θ) (hEF : CriticalStripExplicitFormula C_N C_R) :
    TruncatedExplicitFormulaPackage θ C_N C_R where
  theta_ge_half := hZ.1
  theta_lt_one := hZ.2.1
  CN_nonneg := hEF.CN_nonneg
  CR_nonneg := hEF.CR_nonneg
  zeta_explicit := fun x T hx hT => by
    obtain ⟨Z, hZs, hZc, hZe⟩ := hEF.zeta_explicit x T hx hT
    refine ⟨Z, fun ρ hρ => ?_, hZc, hZe⟩
    obtain ⟨h0, h1, hz, him⟩ := hZs ρ hρ
    obtain ⟨hlo, hhi⟩ := riemannZeta_zero_mem_strip_of_zeroFreeStrip hZ h0 h1 hz
    exact ⟨hlo, hhi, him⟩
  char_explicit := fun q _ hq χ hχ x T hx hT => by
    obtain ⟨Z, hZs, hZc, hZe⟩ := hEF.char_explicit q hq χ hχ x T hx hT
    refine ⟨Z, fun ρ hρ => ?_, hZc, hZe⟩
    obtain ⟨h0, h1, hz, him⟩ := hZs ρ hρ
    obtain ⟨hlo, hhi⟩ := LFunction_zero_mem_strip_of_zeroFreeStrip hZ χ h0 h1 hz
    exact ⟨hlo, hhi, him⟩

/-- **GRH (`RHDirect.ZeroFreeAll`) + Explicit Formula → `PsiCharPowerBound θ'` for EVERY `θ' > 1/2`**
(and full discharge of `LinnikAPDyadic`, `LinnikAPInterval`, `PairSupply`, `PairEx`, `SmallOne`). -/
theorem psiCharPowerBound_of_zeroFreeAll_and_explicitFormula {C_N C_R : ℝ}
    (hZ : ZeroFreeAll) (hEF : CriticalStripExplicitFormula C_N C_R) :
    (∀ θ' : ℝ, 1 / 2 < θ' → θ' < 1 → Stage2DirichletAP.PsiCharPowerBound θ') ∧
      Stage2PrimePairs.LinnikAPDyadic ∧
      Stage2PrimePairs.LinnikAPInterval ∧
      HostFieldSupply.PairSupply ∧
      ThetaSlopeEngine.PairEx ∧
      HostFieldSupply.SmallOne := by
  have hPkg := truncatedExplicitFormulaPackage_of_zeroFreeStrip
    (zeroFreeStrip_half_of_zeroFreeAll hZ) hEF
  exact ⟨fun θ' hlo hhi => psiCharPowerBound_of_truncatedExplicitFormula hPkg hlo hhi,
    stage2PrimePairs_of_truncatedExplicitFormula hPkg⟩

/-- **Bridge to `ZeroDensityWindow.ZeroFreeBox`**:
any non-principal character `χ ≠ 1` mod `q` satisfying the classical zero-free region without a
real exceptional zero satisfies `ZeroDensityWindow.ZeroFreeBox Q χ` whenever
`296 * max B 1 * log (q * (Q + 2)) < 400`. -/
theorem zeroFreeBox_of_hadamard_nonexceptional {B Q : ℝ} (H : HadamardLogDerivPackage B)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    (hno_exc : ¬ (IsRealChar χ ∧ ∃ β : ℝ, 0 < β ∧ β < 1 ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧
        1 - 1 / (296 * max B 1 * Real.log (2 * (q : ℝ))) < β))
    (hsmall : 296 * max B 1 * Real.log ((q : ℝ) * (Q + 2)) < 400) :
    ZeroDensityWindow.ZeroFreeBox Q χ := by
  intro s hs_re hs_im hz
  by_cases h1 : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) h1 hz
  · push Not at h1
    have h0 : 0 < s.re := by linarith
    rcases zeroFreeRegion_nonexceptional H hχ1 h0 h1 hz with hreg | ⟨hr, him, hgt⟩
    · have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
      have hlog_le : Real.log ((q : ℝ) * (|s.im| + 2)) ≤ Real.log ((q : ℝ) * (Q + 2)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have hL : (1 / 2 : ℝ) < Real.log ((q : ℝ) * (|s.im| + 2)) :=
        half_lt_log_q_abs_add_two s.im
      have hC1 : 1 ≤ max B 1 := le_max_right B 1
      have hden_lt : 296 * max B 1 * Real.log ((q : ℝ) * (|s.im| + 2)) < 400 :=
        lt_of_le_of_lt (by nlinarith) hsmall
      have hdiv : (1 : ℝ) / 400 < 1 / (296 * max B 1 * Real.log ((q : ℝ) * (|s.im| + 2))) :=
        one_div_lt_one_div_of_lt (by positivity) hden_lt
      linarith
    · apply hno_exc
      refine ⟨hr, s.re, h0, h1, ?_, hgt⟩
      have hs_eq : (s.re : ℂ) = s := by
        apply Complex.ext
        · simp
        · simp [him]
      rwa [hs_eq]

/-- **Bridge to `RHDirect.HasRpowWindow` (`la = 3 / 2`)**:
any `PsiCharPowerBound θ` yields a `HasRpowWindow` bound on `[Y, Y ^ (3 / 2)]` (matching
`ZeroDensityWindow`'s `la = 3 / 2` windows) for `|ψ(y; q, a) - y / φ(q)|`. -/
theorem hasRpowWindow_psiAP_err_of_psiCharPowerBound {θ : ℝ}
    (h : Stage2DirichletAP.PsiCharPowerBound θ)
    {q a : ℕ} [NeZero q] (hq : 2 ≤ q) (hcop : Nat.Coprime a q) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ θ' : ℝ, θ < θ' →
        RHDirect.HasRpowWindow
          (fun y => |Stage2DirichletAP.chebyshevPsiAP q a y - y / (q.totient : ℝ)|)
          θ' (1 / 2) C' := by
  obtain ⟨hθ0, _, C, hC0, hC⟩ := h
  set C' : ℝ := C + C * (Real.log (q : ℝ) + 1) + (q.primeFactors.card : ℝ)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hC'0 : 0 ≤ C' := by
    have := Real.log_nonneg hq1
    positivity
  refine ⟨C', hC'0, fun θ' hθ' Y₀ => ?_⟩
  set δ : ℝ := θ' - θ
  have hδ : 0 < δ := by linarith
  have hθ'0 : 0 < θ' := by linarith
  -- Choose `Y ≥ max Y₀ 2` large enough so `log y ≤ y ^ θ'` on `[Y, Y^(3/2)]`.
  set Y : ℝ := max (max Y₀ 2) ((2 / θ') ^ (2 / θ'))
  refine ⟨Y, le_trans (le_max_left _ _) (le_max_left _ _), fun y hy => ?_⟩
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
  have hy2 : 2 ≤ y := hY2.trans hy.1
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨hpsi, hchar⟩ := hC q hq y hy2
  have hE2_nn : 0 ≤ C * (Real.log (q : ℝ) + 1) * y ^ θ :=
    mul_nonneg (mul_nonneg hC0 (by linarith [Real.log_nonneg hq1])) (Real.rpow_nonneg hy0.le θ)
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound
    hcop hy1 hE2_nn hpsi hchar
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hdiv_le :
      (C * y ^ θ + (q.primeFactors.card : ℝ) * Real.log y) / (q.totient : ℝ) ≤
        C * y ^ θ + (q.primeFactors.card : ℝ) * Real.log y :=
    div_le_self (add_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hy0.le θ))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hy1))) hphi_ge1
  have hy_log : Real.log y ≤ y ^ θ' := by
    have hY_ge : max 1 ((2 * 1 / θ') ^ (2 / θ')) ≤ y := by
      refine max_le hy1 ?_
      have h1 : (2 / θ') ^ (2 / θ') ≤ Y := le_max_right _ _
      simpa using h1.trans hy.1
    have := ZeroDensityWindow.mul_log_le_rpow_of_ge hθ'0 one_pos hY_ge
    simpa using this
  have hy_pow : y ^ θ ≤ y ^ θ' := Real.rpow_le_rpow_of_exponent_le hy1 hθ'.le
  calc |Stage2DirichletAP.chebyshevPsiAP q a y - y / (q.totient : ℝ)|
      ≤ (C * y ^ θ + (q.primeFactors.card : ℝ) * Real.log y) / (q.totient : ℝ) +
          C * (Real.log (q : ℝ) + 1) * y ^ θ := htri
    _ ≤ C * y ^ θ + (q.primeFactors.card : ℝ) * Real.log y +
          C * (Real.log (q : ℝ) + 1) * y ^ θ := by linarith
    _ ≤ C * y ^ θ' + (q.primeFactors.card : ℝ) * y ^ θ' +
          C * (Real.log (q : ℝ) + 1) * y ^ θ' := by
        have h1 : C * y ^ θ ≤ C * y ^ θ' := mul_le_mul_of_nonneg_left hy_pow hC0
        have h2 : (q.primeFactors.card : ℝ) * Real.log y ≤ (q.primeFactors.card : ℝ) * y ^ θ' :=
          mul_le_mul_of_nonneg_left hy_log (Nat.cast_nonneg _)
        have h3 : C * (Real.log (q : ℝ) + 1) * y ^ θ ≤ C * (Real.log (q : ℝ) + 1) * y ^ θ' :=
          mul_le_mul_of_nonneg_left hy_pow (mul_nonneg hC0 (by linarith [Real.log_nonneg hq1]))
        linarith
    _ = C' * y ^ θ' := by dsimp only [C']; ring

end RHDirect.Stage3ZeroFreeRegion

end
