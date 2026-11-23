import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.Stage2PrimePairs
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# RHDirect.Stage2DirichletAP

Compact, self-contained, 0-`sorry`, 0-custom-`axiom` Lean 4 formalization of the
**Dirichlet Primes-in-Arithmetic-Progressions & Quantitative Prime-Counting Bridge**
against `RHDirect.Interfaces`, `RHDirect.ElementaryEquiv`, `RHDirect.Stage2PrimePairs`,
and targeted Mathlib `v4.33.1`.

## Contents
1. **Nonvanishing on `Re(s) ≥ 1`, Pole Cancellation & Qualitative Dirichlet Theorem**:
   - Direct bridges to `DirichletCharacter.LFunction_ne_zero_of_one_le_re`,
     `DirichletCharacter.LFunction_apply_one_ne_zero`, and the 3-4-1 product bound
     `DirichletCharacter.norm_LFunction_product_ge_one`.
   - Residue-class logarithmic-derivative `L`-series identity and continuity of the
     pole-cancelled auxiliary function `LFunctionResidueClassAux` on `Re(s) ≥ 1`.
   - Unconditional infinitude of primes `p ≡ a [MOD q]` for all `q ≥ 1` and `Nat.Coprime a q`,
     plus direct unconditional infinitude of primes `d` satisfying `Stage2PrimePairs`'s full
     CRT odd-primorial congruence `d ≡ pairResidue q n [MOD pairModulus q n]`.
2. **Exact Character-Orthogonality Indicator for Residue Classes `n ≡ a [MOD q]`**:
   - Conjugate identity `starRingEnd ℂ (χ a) = χ a⁻¹` for units `a : ZMod q`.
   - Complex and real orthogonality indicators:
     `(φ(q))⁻¹ * ∑ χ, conj(χ a) * χ n = if n ≡ a [MOD q] then 1 else 0`.
   - Principal character evaluation `(1 : DirichletCharacter ℂ q) n = 1_{Coprime n q}`.
3. **Residue-Class Chebyshev Sums `ψ(x; q, a)`, `θ(x; q, a)`, `π(x; q, a)` & Character Decomposition**:
   - Exact character-sum decomposition of `chebyshevPsiAP q a x` and `chebyshevRampAP q a y`
     (bridging directly to `RHDirect.ramp`).
   - Exact principal + non-principal split separating `chebyshevPsiCoprime q x / φ(q)` from
     `∑_{χ ≠ 1} conj(χ a) * ψ(x, χ)`.
   - Sharp unconditional prime-power-dividing-`q` bound:
     `0 ≤ ψ(x) - ψ_coprime(x; q) ≤ ω(q) * log x ≤ (log q / log 2) * log x`.
   - Triangle-inequality error transfer from character-sum bounds to `|ψ(x; q, a) - x / φ(q)|`.
4. **Sharp Prime-Power Bound `ψ(x) - θ(x) ≤ √x log x` & Quantitative Prime Extraction**:
   - Unconditional bound `0 ≤ ψ(x) - θ(x) ≤ √x * log x` and residue-class analogue
     `0 ≤ ψ(x; q, a) - θ(x; q, a) ≤ √x * log x` for all `x ≥ 1`.
   - Exact quantitative prime-counting lower bound on `(X, B]`:
     `(π(B; q, a) - π(X; q, a)) * log B ≥ (ψ(B; q, a) - ψ(X; q, a)) - √B * log B`.
   - Exact prime-existence theorems `exists_prime_in_Ioc_of_psiAP_diff_gt` and
     `exists_prime_le_of_psiAP_gt` (least prime `p ≡ a [MOD q]` with `p ≤ B`).
5. **Direct Quantitative Reduction to `Stage2PrimePairs`'s Linnik Hypotheses**:
   - `PsiAPRelativeBound → Stage2PrimePairs.LinnikAPDyadic → Stage2PrimePairs.LinnikAPInterval`.
   - `PsiCharPowerBound θ → PsiAPRelativeBound` (showing any uniform power-saving / zero-free
     bound `|ψ(x) - x| ≤ C x^θ`, `‖ψ(x, χ)‖ ≤ C (log q + 1) x^θ` with `θ < 1` directly
     discharges `LinnikAPDyadic`, `LinnikAPInterval`, `HostFieldSupply.PairSupply`,
     `ThetaSlopeEngine.PairEx`, and `HostFieldSupply.SmallOne`!).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex DirichletCharacter Finset RHDirect
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage2DirichletAP

/-! ## Section 1: Nonvanishing on `Re(s) ≥ 1`, Pole Cancellation & Qualitative Dirichlet Theorem -/

/-- Nonvanishing of Dirichlet `L`-functions on the closed half-plane `Re(s) ≥ 1`
(re-exported cleanly from Mathlib's de la Vallée Poussin / Hadamard proof). -/
theorem LFunction_ne_zero_of_one_le_re_bridge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

/-- Nonvanishing at `s = 1` for every non-principal Dirichlet character `χ ≠ 1`. -/
theorem LFunction_apply_one_ne_zero_bridge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- De la Vallée Poussin 3-4-1 product lower bound `‖L(1, 1+x)³ · L(χ, 1+x+iy)⁴ · L(χ², 1+x+2iy)‖ ≥ 1`
for all `x > 0` and `y ∈ ℝ`. -/
theorem norm_LFunction_three_four_one_ge_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖LFunction (1 : DirichletCharacter ℂ q) (1 + x) ^ 3 *
          LFunction χ (1 + x + I * y) ^ 4 *
          LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ :=
  DirichletCharacter.norm_LFunction_product_ge_one χ hx y

/-- Residue-class logarithmic-derivative `L`-series identity on `Re(s) > 1`:
`∑_{n ≡ a [MOD q]} Λ(n) n^(-s) = -φ(q)⁻¹ ∑_χ χ(a⁻¹) L'(χ, s) / L(χ, s)`. -/
theorem LSeries_residueClass_eq_logDeriv_sum {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) s =
      -(q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (deriv (LFunction χ) s / LFunction χ s) :=
  ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq ha hs

/-- Pole cancellation on `Re(s) ≥ 1`: the auxiliary function
`LFunctionResidueClassAux a` agrees with `LSeries (residueClass a) s - φ(q)⁻¹ / (s - 1)`
for `Re(s) > 1` and extends continuously to the closed half-plane `Re(s) ≥ 1`. -/
theorem LFunctionResidueClassAux_continuous_and_eq {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    ContinuousOn (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a)
        {s : ℂ | 1 ≤ s.re} ∧
      Set.EqOn
        (fun s =>
          LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass a n : ℂ)) s -
            (q.totient : ℂ)⁻¹ / (s - 1))
        (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a)
        {s : ℂ | 1 < s.re} :=
  ⟨ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux a,
   (ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux ha).symm⟩

/-- **Dirichlet's Theorem on Primes in Arithmetic Progressions** (set-infinitude form):
for any `q ≥ 1` and `Nat.Coprime a q`, infinitely many primes satisfy `p ≡ a [MOD q]`. -/
theorem dirichlet_infinite_primes_modEq {q a : ℕ} (hq : q ≠ 0) (hcop : Nat.Coprime a q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  Nat.infinite_setOfPred_prime_and_modEq hq hcop

/-- **Dirichlet's Theorem on Primes in Arithmetic Progressions** (unbounded witness form):
for any `q ≥ 1`, `Nat.Coprime a q`, and threshold `B : ℕ`, there exists a prime `p > B`
with `p ≡ a [MOD q]`. -/
theorem dirichlet_exists_prime_gt_modEq {q a : ℕ} (hq : q ≠ 0) (hcop : Nat.Coprime a q)
    (B : ℕ) : ∃ p : ℕ, B < p ∧ p.Prime ∧ p ≡ a [MOD q] :=
  Nat.forall_exists_prime_gt_and_modEq B hq hcop

/-- **Unconditional Infinitude of Full-CRT Auxiliary Primes `d`** for `Stage2PrimePairs`:
for any `q % 8 = 3`, any odd-primorial cutoff `n : ℕ`, and any lower bound `B : ℕ`,
there unconditionally exists a prime `d > B` satisfying `d ≡ pairResidue q n [MOD pairModulus q n]`
(hence `d % 16 = 7`, `q ∣ d + 1`, and `p ∣ d + 1` for every odd prime `p ≤ n`). -/
theorem exists_prime_gt_pairModEq {q : ℕ} (hq8 : q % 8 = 3) (n B : ℕ) :
    ∃ d : ℕ, B < d ∧ d.Prime ∧
      d ≡ Stage2PrimePairs.pairResidue q n [MOD Stage2PrimePairs.pairModulus q n] ∧
      d % 16 = 7 ∧ q ∣ d + 1 ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ d + 1) := by
  have hmod_ne : Stage2PrimePairs.pairModulus q n ≠ 0 := by
    have := Stage2PrimePairs.two_le_pairModulus (n := n) hq8
    omega
  obtain ⟨d, hBd, hd_prime, hd_mod⟩ :=
    dirichlet_exists_prime_gt_modEq hmod_ne
      (Stage2PrimePairs.coprime_pairResidue_pairModulus hq8) B
  obtain ⟨hd16, hqd, hsmall⟩ := Stage2PrimePairs.pairModEq_imp hq8 hd_mod
  exact ⟨d, hBd, hd_prime, hd_mod, hd16, hqd, hsmall⟩

/-! ## Section 2: Exact Character-Orthogonality Indicator for Residue Classes `n ≡ a [MOD q]` -/

/-- For any unit `a : ZMod q`, complex conjugation of `χ a` equals `χ (a⁻¹)`. -/
theorem conj_dirichletChar_eq_apply_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) :
    starRingEnd ℂ (χ a) = χ a⁻¹ := by
  have hstar : starRingEnd ℂ (χ a) = (χ a)⁻¹ := by
    have h1 : starRingEnd ℂ (χ a) = χ⁻¹ a := by
      simpa [RCLike.star_def] using MulChar.star_apply' χ a
    exact h1.trans (MulChar.inv_apply_eq_inv' χ a)
  rw [hstar]
  have hmul : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl, map_one]
  exact (eq_inv_of_mul_eq_one_left hmul).symm

/-- For `Nat.Coprime a q`, the cast `(a : ZMod q)` is a unit. -/
theorem isUnit_zmod_of_coprime {q a : ℕ} (hcop : Nat.Coprime a q) :
    IsUnit (a : ZMod q) :=
  (ZMod.isUnit_iff_coprime a q).mpr hcop

/-- **Exact Character-Orthogonality Indicator on `ZMod q`**:
for any unit `a : ZMod q` and any `b : ZMod q`,
`(φ(q))⁻¹ * ∑_{χ mod q} conj(χ a) * χ b = 1_{b = a}`. -/
theorem char_orthogonality_indicator_zmod {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (b : ZMod q) :
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
      if b = a then 1 else 0 := by
  have hphi_ne : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum :
      ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
        if a = b then (q.totient : ℂ) else 0 := by
    have hcongr :
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
          ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b :=
      Finset.sum_congr rfl fun χ _ => by rw [conj_dirichletChar_eq_apply_inv χ ha]
    rw [hcongr]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  rw [hsum]
  by_cases hba : b = a
  · subst hba
    simp [hphi_ne]
  · have hab : a ≠ b := Ne.symm hba
    simp [hba, hab]

/-- **Exact Character-Orthogonality Indicator for Residue Classes `n ≡ a [MOD q]`**:
for `q ≥ 1` (`[NeZero q]`), `Nat.Coprime a q`, and any `n : ℕ`,
`(φ(q))⁻¹ * ∑_{χ mod q} conj(χ a) * χ n = if n ≡ a [MOD q] then 1 else 0`. -/
theorem char_orthogonality_indicator_nat {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) :
    (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q) =
      if n ≡ a [MOD q] then 1 else 0 := by
  have h := char_orthogonality_indicator_zmod (isUnit_zmod_of_coprime hcop) (n : ZMod q)
  simpa only [ZMod.natCast_eq_natCast_iff] using h

/-- Real-part form of the character-orthogonality indicator for `n ≡ a [MOD q]`. -/
theorem char_orthogonality_indicator_nat_re {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    (n : ℕ) :
    (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q)).re =
      if n ≡ a [MOD q] then 1 else 0 := by
  have h := congrArg Complex.re (char_orthogonality_indicator_nat hcop n)
  have hphi : ((q.totient : ℂ)⁻¹).re = (q.totient : ℝ)⁻¹ := by simp
  have hphi_im : ((q.totient : ℂ)⁻¹).im = 0 := by simp
  rw [Complex.mul_re, hphi, hphi_im, zero_mul, sub_zero, Complex.re_sum] at h
  by_cases hmod : n ≡ a [MOD q] <;> simp [hmod] at h ⊢ <;> exact h

/-- Principal Dirichlet character evaluation: `(1 : DirichletCharacter ℂ q) n = 1_{Coprime n q}`. -/
theorem principal_char_apply_nat {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if Nat.Coprime n q then 1 else 0 := by
  by_cases hcop : Nat.Coprime n q
  · simp [hcop, MulChar.one_apply (isUnit_zmod_of_coprime hcop)]
  · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
    simp [hcop, MulChar.map_nonunit _ hnu]

/-! ## Section 3: Residue-Class Chebyshev Sums `ψ(x; q, a)`, `θ(x; q, a)` & Character Decomposition -/

/-- Residue-class Chebyshev prime-power sum `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a [MOD q]} Λ(n)`. -/
def chebyshevPsiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n ≡ a [MOD q] then Λ n else 0

/-- Residue-class Chebyshev prime sum `θ(x; q, a) = ∑_{p ≤ x, p prime, p ≡ a [MOD q]} log p`. -/
def chebyshevThetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0

/-- Global Chebyshev prime sum `θ(x) = ∑_{p ≤ x, p prime} log p`. -/
def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime then Real.log (n : ℝ) else 0

/-- Prime-counting function in an arithmetic progression:
`π(x; q, a) = #{p ≤ x : p.Prime ∧ p ≡ a [MOD q]}`. -/
def primeCountAP (q a : ℕ) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ a [MOD q]).card

/-- Character-twisted Chebyshev sum `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
def chebyshevPsiChar {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ (n : ZMod q) * (Λ n : ℂ)

/-- Principal-character (coprime-to-`q`) Chebyshev sum `ψ_coprime(x; q) = ∑_{n ≤ x, (n, q) = 1} Λ(n)`. -/
def chebyshevPsiCoprime (q : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if Nat.Coprime n q then Λ n else 0

/-- Residue-class Cesàro-1 / Riesz ramp sum `∑_{n ≤ y, n ≡ a [MOD q]} Λ(n) (y/n - 1)_+`. -/
def chebyshevRampAP (q a : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
    if n ≡ a [MOD q] then Λ n * max (y / (n : ℝ) - 1) 0 else 0

theorem chebyshevPsiAP_nonneg (q a : ℕ) (x : ℝ) : 0 ≤ chebyshevPsiAP q a x :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl]

theorem chebyshevPsiAP_mono {q a : ℕ} {x y : ℝ} (hxy : x ≤ y) :
    chebyshevPsiAP q a x ≤ chebyshevPsiAP q a y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxy) 1)
  · intro _ _ _; split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl]

theorem chebyshevPsiAP_one (q a : ℕ) : chebyshevPsiAP q a 1 = 0 := by
  simp [chebyshevPsiAP, Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_one]

theorem chebyshevThetaAP_nonneg (q a : ℕ) (x : ℝ) : 0 ≤ chebyshevThetaAP q a x :=
  Finset.sum_nonneg fun n _ => by
    split_ifs with h
    · exact Real.log_natCast_nonneg n
    · exact le_rfl

theorem chebyshevThetaAP_le_chebyshevPsiAP (q a : ℕ) (x : ℝ) :
    chebyshevThetaAP q a x ≤ chebyshevPsiAP q a x := by
  apply Finset.sum_le_sum
  intro n _
  by_cases hmod : n ≡ a [MOD q]
  · by_cases hp : n.Prime
    · simp [hmod, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hmod, hp, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [hmod]

/-- Exact character-sum decomposition of `ψ(x; q, a)`:
`ψ(x; q, a) = φ(q)⁻¹ ∑_{χ mod q} conj(χ a) * ψ(x, χ)`. -/
theorem chebyshevPsiAP_eq_char_sum {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (x : ℝ) :
    (chebyshevPsiAP q a x : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x := by
  unfold chebyshevPsiAP chebyshevPsiChar
  rw [Complex.ofReal_sum]
  calc
    ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ((if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ)
        = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ((q.totient : ℂ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q)) *
            (Λ n : ℂ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [char_orthogonality_indicator_nat hcop n]
          split_ifs <;> simp
    _ = (q.totient : ℂ)⁻¹ *
          ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ∑ χ : DirichletCharacter ℂ q,
              starRingEnd ℂ (χ (a : ZMod q)) * (χ (n : ZMod q) * (Λ n : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
    _ = (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            starRingEnd ℂ (χ (a : ZMod q)) *
              ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ (n : ZMod q) * (Λ n : ℂ) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]

/-- Exact character-sum decomposition of the residue-class Cesàro ramp sum,
bridging directly into `RHDirect.ramp` from `RHDirect.Interfaces`. -/
theorem chebyshevRampAP_eq_ramp_sum {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (y : ℝ) :
    (chebyshevRampAP q a y : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          starRingEnd ℂ (χ (a : ZMod q)) * RHDirect.ramp (fun n => χ (n : ZMod q)) y := by
  unfold chebyshevRampAP RHDirect.ramp
  rw [Complex.ofReal_sum]
  calc
    ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
        ((if n ≡ a [MOD q] then Λ n * max (y / (n : ℝ) - 1) 0 else 0 : ℝ) : ℂ)
        = ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
            ((q.totient : ℂ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q)) *
            ((Λ n : ℂ) * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [char_orthogonality_indicator_nat hcop n]
          split_ifs <;> simp
    _ = (q.totient : ℂ)⁻¹ *
          ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
            ∑ χ : DirichletCharacter ℂ q,
              starRingEnd ℂ (χ (a : ZMod q)) *
                ((Λ n : ℂ) * χ (n : ZMod q) * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
    _ = (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            starRingEnd ℂ (χ (a : ZMod q)) *
              ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
                (Λ n : ℂ) * χ (n : ZMod q) * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]

/-- The principal character Chebyshev sum `ψ(x, 1_q)` equals `chebyshevPsiCoprime q x`. -/
theorem chebyshevPsiChar_one_eq_coprime (q : ℕ) (x : ℝ) :
    chebyshevPsiChar (1 : DirichletCharacter ℂ q) x = (chebyshevPsiCoprime q x : ℂ) := by
  unfold chebyshevPsiChar chebyshevPsiCoprime
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [principal_char_apply_nat]
  split_ifs <;> simp

open Classical in
/-- **Principal + Non-Principal Character Decomposition of `ψ(x; q, a)`** (complex form):
`ψ(x; q, a) = φ(q)⁻¹ * ψ_coprime(x; q) + φ(q)⁻¹ * ∑_{χ ≠ 1} conj(χ a) * ψ(x, χ)`. -/
theorem chebyshevPsiAP_eq_principal_add_nonprincipal {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) (x : ℝ) :
    (chebyshevPsiAP q a x : ℂ) =
      (q.totient : ℂ)⁻¹ * (chebyshevPsiCoprime q x : ℂ) +
        (q.totient : ℂ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x := by
  rw [chebyshevPsiAP_eq_char_sum hcop x]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x) (Finset.mem_univ 1)
  rw [← hsplit, mul_add]
  congr 1
  have h1 : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 :=
    MulChar.one_apply (isUnit_zmod_of_coprime hcop)
  rw [h1, map_one, one_mul, chebyshevPsiChar_one_eq_coprime]

open Classical in
/-- **Principal + Non-Principal Character Decomposition of `ψ(x; q, a)`** (real form):
`ψ(x; q, a) = ψ_coprime(x; q) / φ(q) + φ(q)⁻¹ * ∑_{χ ≠ 1} Re(conj(χ a) * ψ(x, χ))`. -/
theorem chebyshevPsiAP_eq_principal_add_nonprincipal_re {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) (x : ℝ) :
    chebyshevPsiAP q a x =
      chebyshevPsiCoprime q x / (q.totient : ℝ) +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
  have h := congrArg Complex.re (chebyshevPsiAP_eq_principal_add_nonprincipal hcop x)
  rw [Complex.ofReal_re, Complex.add_re] at h
  have h1 : ((q.totient : ℂ)⁻¹ * (chebyshevPsiCoprime q x : ℂ)).re =
      chebyshevPsiCoprime q x / (q.totient : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
      div_eq_inv_mul]
  have h2 :
      ((q.totient : ℂ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re =
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  rw [h1, h2] at h
  exact h

private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
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

private lemma log_pow_natLog_le {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) :
    (Nat.log p N : ℝ) * Real.log (p : ℝ) ≤ Real.log x := by
  have hpow : p ^ Nat.log p N ≤ N := Nat.pow_log_le_self p (by omega)
  have hpowR : ((p : ℝ) ^ Nat.log p N) ≤ x :=
    le_trans (by exact_mod_cast hpow) hNx
  have hpos : (0 : ℝ) < (p : ℝ) ^ Nat.log p N := pow_pos (Nat.cast_pos.mpr hp.pos) _
  calc (Nat.log p N : ℝ) * Real.log (p : ℝ)
      = Real.log ((p : ℝ) ^ Nat.log p N) := (Real.log_pow (p : ℝ) (Nat.log p N)).symm
    _ ≤ Real.log x := Real.log_le_log hpos hpowR

private lemma sum_vonMangoldt_primePow_le_log {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (a : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ (Finset.Icc a (Nat.log p N)).image (fun k => p ^ k), Λ n ≤ Real.log x := by
  calc ∑ n ∈ (Finset.Icc a (Nat.log p N)).image (fun k => p ^ k), Λ n
      ≤ ∑ k ∈ Finset.Icc a (Nat.log p N), Λ (p ^ k) :=
        Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ _k ∈ Finset.Icc a (Nat.log p N), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk0 : k ≠ 0 := by
          rw [Finset.mem_Icc] at hk; omega
        rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ = ((Finset.Icc a (Nat.log p N)).card : ℝ) * Real.log (p : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log p N : ℝ) * Real.log (p : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
        have hcard : (Finset.Icc a (Nat.log p N)).card ≤ Nat.log p N := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast hcard
    _ ≤ Real.log x := log_pow_natLog_le hp hN hNx

/-- Elementary prime-factor count bound `2 ^ ω(q) ≤ q` for `q ≥ 1`. -/
theorem two_pow_card_primeFactors_le {q : ℕ} (hq : 0 < q) :
    2 ^ q.primeFactors.card ≤ q := by
  have h1 : 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
    rw [Finset.prod_const]
  rw [h1]
  calc ∏ _p ∈ q.primeFactors, (2 : ℕ)
      ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

/-- Elementary logarithmic bound `ω(q) ≤ log q / log 2` for `q ≥ 1`. -/
theorem card_primeFactors_le_log_div_log_two {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have hle : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_card_primeFactors_le hq
  calc (q.primeFactors.card : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ q.primeFactors.card) := (Real.log_pow 2 q.primeFactors.card).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (by positivity) hle

/-- Unconditional bound on the difference `ψ(x) - ψ_coprime(x; q)` coming from prime powers
dividing `q`: `0 ≤ ψ(x) - ψ_coprime(x; q) ≤ ω(q) * log x` for all `x ≥ 1` and `q ≥ 1`. -/
theorem chebyshevPsi_sub_chebyshevPsiCoprime_bounds {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ chebyshevPsi x - chebyshevPsiCoprime q x ∧
      chebyshevPsi x - chebyshevPsiCoprime q x ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  have hdiff :
      chebyshevPsi x - chebyshevPsiCoprime q x =
        ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n), Λ n := by
    unfold chebyshevPsi chebyshevPsiCoprime
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop, if_neg (fun h => h.1 hcop), sub_self]
    · by_cases hpp : IsPrimePow n
      · rw [if_neg hcop, if_pos ⟨hcop, hpp⟩, sub_zero]
      · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
        rw [if_neg hcop, if_neg (fun h => hpp h.2), sub_zero, h0]
  rw [hdiff]
  refine ⟨Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsub :
      (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n) ⊆
        q.primeFactors.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnle, hncop, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      have hpcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
      exact hncop (hpcop.pow_left k)
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩, k, ⟨hkpos, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  calc ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n), Λ n
      ≤ ∑ n ∈ q.primeFactors.biUnion
          (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
        sum_biUnion_le_of_nonneg _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact sum_vonMangoldt_primePow_le_log (Nat.prime_of_mem_primeFactors hp) hN hNx 1 le_rfl
    _ = (q.primeFactors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Logarithmic form of the coprime-Chebyshev difference bound:
`ψ(x) - ψ_coprime(x; q) ≤ (log q / log 2) * log x` for all `q ≥ 1` and `x ≥ 1`. -/
theorem chebyshevPsi_sub_chebyshevPsiCoprime_le_log {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsi x - chebyshevPsiCoprime q x ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x :=
  (chebyshevPsi_sub_chebyshevPsiCoprime_bounds hq hx).2.trans
    (mul_le_mul_of_nonneg_right (card_primeFactors_le_log_div_log_two hq) (Real.log_nonneg hx))

open Classical in
/-- **Exact Triangle-Inequality Reduction from Character Sums to `|ψ(x; q, a) - x / φ(q)|`**:
bounds `|ψ(x; q, a) - x / φ(q)|` explicitly in terms of `|ψ(x) - x|`, `ω(q) log x`, and
the non-principal character sums `‖ψ(x, χ)‖`. -/
theorem abs_chebyshevPsiAP_sub_le_of_char_sums {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    {x : ℝ} (hx : 1 ≤ x) :
    |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [chebyshevPsiAP_eq_principal_add_nonprincipal_re hcop x]
  have hsplit :
      chebyshevPsiCoprime q x / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re -
          x / (q.totient : ℝ) =
        ((chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)) / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
    ring
  rw [hsplit]
  have h1 :
      |((chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)) / (q.totient : ℝ)| ≤
        (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) := by
    rw [abs_div, abs_of_pos hphi_pos]
    refine div_le_div_of_nonneg_right ?_ hphi_pos.le
    obtain ⟨hnn, hup⟩ := chebyshevPsi_sub_chebyshevPsiCoprime_bounds (NeZero.pos q) hx
    calc |(chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)|
        ≤ |chebyshevPsi x - x| + |chebyshevPsi x - chebyshevPsiCoprime q x| := abs_sub _ _
      _ = |chebyshevPsi x - x| + (chebyshevPsi x - chebyshevPsiCoprime q x) := by
          rw [abs_of_nonneg hnn]
      _ ≤ |chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x := by linarith
  have h2 :
      |(q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re| ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hphi_pos)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
    calc |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re|
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            |(starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
          refine Finset.sum_le_sum fun χ _ => ?_
          calc |(starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re|
              ≤ ‖starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x‖ := Complex.abs_re_le_norm _
            _ = ‖χ (a : ZMod q)‖ * ‖chebyshevPsiChar χ x‖ := by
                rw [norm_mul, Complex.norm_conj]
            _ ≤ 1 * ‖chebyshevPsiChar χ x‖ :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
            _ = ‖chebyshevPsiChar χ x‖ := one_mul _
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Uniform character-sum corollary: if `|ψ(x) - x| ≤ E₁` and `‖ψ(x, χ)‖ ≤ E₂` for all `χ ≠ 1`,
then `|ψ(x; q, a) - x / φ(q)| ≤ (E₁ + ω(q) log x) / φ(q) + E₂`. -/
theorem abs_chebyshevPsiAP_sub_le_of_uniform_char_bound {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) {x E₁ E₂ : ℝ} (hx : 1 ≤ x) (hE₂ : 0 ≤ E₂)
    (h1 : |chebyshevPsi x - x| ≤ E₁)
    (h2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖chebyshevPsiChar χ x‖ ≤ E₂) :
    |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      (E₁ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) + E₂ := by
  classical
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hbase := abs_chebyshevPsiAP_sub_le_of_char_sums hcop hx
  have hfirst :
      (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
        (E₁ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hphi_pos.le
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
    have htot : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
        ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card (Finset.erase_subset _ _)
      _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
      _ = q.totient := htot
  have hsecond :
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ ≤ E₂ := by
    calc (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖
        ≤ (q.totient : ℝ)⁻¹ *
            ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), E₂ := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
          exact Finset.sum_le_sum fun χ hχ => h2 χ (Finset.mem_erase.mp hχ).1
      _ = (q.totient : ℝ)⁻¹ *
            (((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * E₂) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * E₂) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE₂
      _ = E₂ := by field_simp [hphi_pos.ne']
  linarith

/-! ## Section 4: Sharp Prime-Power Bound `ψ(x) - θ(x) ≤ √x log x` & Quantitative Prime Extraction -/

/-- **Sharp Unconditional Proper-Prime-Power Bound**:
for all `x ≥ 1`, `0 ≤ ψ(x) - θ(x) ≤ √x * log x`. -/
theorem chebyshevPsi_sub_chebyshevTheta_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ chebyshevPsi x - chebyshevTheta x ∧
      chebyshevPsi x - chebyshevTheta x ≤ Real.sqrt x * Real.log x := by
  have hdiff :
      chebyshevPsi x - chebyshevTheta x =
        ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n), Λ n := by
    unfold chebyshevPsi chebyshevTheta
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · by_cases hpp : IsPrimePow n
      · simp [hp, hpp]
      · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
        simp [hp, hpp, h0]
  rw [hdiff]
  refine ⟨Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  set P : Finset ℕ := (Finset.Icc 2 (Nat.sqrt ⌊x⌋₊)).filter Nat.Prime
  have hsub :
      (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n) ⊆
        P.biUnion (fun p => (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc, P] at hn ⊢
    obtain ⟨hnle, hnp, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hnp
      exact hnp hp
    have hp2_le : p * p ≤ ⌊x⌋₊ := by
      have hsq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      rw [sq] at hsq
      omega
    have hp_sqrt : p ≤ Nat.sqrt ⌊x⌋₊ := Nat.le_sqrt.mpr hp2_le
    refine ⟨p, ⟨⟨hp.two_le, hp_sqrt⟩, hp⟩, k, ⟨hk2, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hP_card : (P.card : ℝ) ≤ Real.sqrt x := by
    have hcard_nat : P.card ≤ Nat.sqrt ⌊x⌋₊ := by
      calc P.card ≤ (Finset.Icc 2 (Nat.sqrt ⌊x⌋₊)).card := Finset.card_filter_le _ _
        _ ≤ Nat.sqrt ⌊x⌋₊ := by rw [Nat.card_Icc]; omega
    have hsqrt_le : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
      have hsq : (Nat.sqrt ⌊x⌋₊ : ℝ) ^ 2 ≤ x := by
        have hnat : Nat.sqrt ⌊x⌋₊ * Nat.sqrt ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.sqrt_le ⌊x⌋₊
        have hR : (Nat.sqrt ⌊x⌋₊ : ℝ) * (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
          exact_mod_cast hnat
        rw [sq]
        exact hR.trans hNx
      exact Real.le_sqrt_of_sq_le hsq
    exact (by exact_mod_cast hcard_nat : (P.card : ℝ) ≤ (Nat.sqrt ⌊x⌋₊ : ℝ)).trans hsqrt_le
  calc ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n), Λ n
      ≤ ∑ n ∈ P.biUnion (fun p => (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ p ∈ P, ∑ n ∈ (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
        sum_biUnion_le_of_nonneg _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ P, Real.log x := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpr : p.Prime := (Finset.mem_filter.mp hp).2
        exact sum_vonMangoldt_primePow_le_log hpr hN hNx 2 (by norm_num)
    _ = (P.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt x * Real.log x :=
        mul_le_mul_of_nonneg_right hP_card (Real.log_nonneg hx)

/-- **Residue-Class Proper-Prime-Power Bound**:
for all `q a : ℕ` and `x ≥ 1`, `0 ≤ ψ(x; q, a) - θ(x; q, a) ≤ √x * log x`. -/
theorem chebyshevPsiAP_sub_chebyshevThetaAP_le (q a : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsiAP q a x - chebyshevThetaAP q a x ≤ Real.sqrt x * Real.log x := by
  have hle : chebyshevPsiAP q a x - chebyshevThetaAP q a x ≤ chebyshevPsi x - chebyshevTheta x := by
    unfold chebyshevPsiAP chebyshevThetaAP chebyshevPsi chebyshevTheta
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hmod : n ≡ a [MOD q]
    · by_cases hp : n.Prime <;> simp [hmod, hp]
    · by_cases hp : n.Prime
      · simp [hmod, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp [hmod, hp, ArithmeticFunction.vonMangoldt_nonneg]
  exact hle.trans (chebyshevPsi_sub_chebyshevTheta_bounds hx).2

/-- Interval difference of `chebyshevThetaAP` is bounded above by the prime count in `(X, B]`
times `log B`. -/
theorem chebyshevThetaAP_diff_le_primeCountAP_mul_log (q a : ℕ) {X B : ℝ}
    (hX : 1 ≤ X) (hXB : X ≤ B) :
    chebyshevThetaAP q a B - chebyshevThetaAP q a X ≤
      ((primeCountAP q a B - primeCountAP q a X : ℕ) : ℝ) * Real.log B := by
  have hfl : ⌊X⌋₊ + 1 ≤ ⌊B⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono hXB) 1
  have hsub_range : Finset.range (⌊X⌋₊ + 1) ⊆ Finset.range (⌊B⌋₊ + 1) := Finset.range_mono hfl
  have hB1 : 1 ≤ B := hX.trans hXB
  have htheta_diff :
      chebyshevThetaAP q a B - chebyshevThetaAP q a X =
        ∑ n ∈ (Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)),
          if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0 := by
    unfold chebyshevThetaAP
    exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub_range)).symm
  have hcard_diff :
      primeCountAP q a B - primeCountAP q a X =
        ((Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)).filter
          fun p => p.Prime ∧ p ≡ a [MOD q]).card := by
    unfold primeCountAP
    have hsub_filt :
        (Finset.range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
          (Finset.range (⌊B⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) :=
      Finset.filter_subset_filter _ hsub_range
    have hsdiff_eq :
        ((Finset.range (⌊B⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) \
            ((Finset.range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) =
          (Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)).filter
            (fun p => p.Prime ∧ p ≡ a [MOD q]) := by
      ext p; simp only [Finset.mem_sdiff, Finset.mem_filter]; tauto
    rw [← hsdiff_eq, Finset.card_sdiff_of_subset hsub_filt]
  rw [htheta_diff, hcard_diff, ← Finset.sum_filter]
  calc ∑ n ∈ (Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)).filter
          (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log (n : ℝ)
      ≤ ∑ _n ∈ (Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)).filter
          (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log B := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range] at hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2.1.pos
        have hn_le : (n : ℝ) ≤ B :=
          le_trans (by exact_mod_cast (by omega : n ≤ ⌊B⌋₊)) (Nat.floor_le (by linarith))
        exact Real.log_le_log hn_pos hn_le
    _ = (((Finset.range (⌊B⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1)).filter
          (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) * Real.log B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Quantitative Prime-Counting Lower Bound on `(X, B]`**:
for `1 ≤ X ≤ B`,
`((π(B; q, a) - π(X; q, a)) : ℝ) * log B ≥ (ψ(B; q, a) - ψ(X; q, a)) - √B * log B`. -/
theorem primeCountAP_diff_mul_log_ge (q a : ℕ) {X B : ℝ} (hX : 1 ≤ X) (hXB : X ≤ B) :
    (chebyshevPsiAP q a B - chebyshevPsiAP q a X) - Real.sqrt B * Real.log B ≤
      ((primeCountAP q a B - primeCountAP q a X : ℕ) : ℝ) * Real.log B := by
  have hB1 : 1 ≤ B := hX.trans hXB
  have h1 : chebyshevThetaAP q a X ≤ chebyshevPsiAP q a X :=
    chebyshevThetaAP_le_chebyshevPsiAP q a X
  have h2 : chebyshevPsiAP q a B - chebyshevThetaAP q a B ≤ Real.sqrt B * Real.log B :=
    chebyshevPsiAP_sub_chebyshevThetaAP_le q a hB1
  have h3 := chebyshevThetaAP_diff_le_primeCountAP_mul_log q a hX hXB
  linarith

/-- **Exact Quantitative Prime-Existence Theorem on `(X, B]`**:
if `1 ≤ X ≤ B` and `√B * log B < ψ(B; q, a) - ψ(X; q, a)`, then there exists a prime
`p ≡ a [MOD q]` strictly inside `(X, B]`. -/
theorem exists_prime_in_Ioc_of_psiAP_diff_gt (q a : ℕ) {X B : ℝ} (hX : 1 ≤ X) (hXB : X ≤ B)
    (hgt : Real.sqrt B * Real.log B < chebyshevPsiAP q a B - chebyshevPsiAP q a X) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ B := by
  have hB1 : 1 ≤ B := hX.trans hXB
  have hpos : 0 < ((primeCountAP q a B - primeCountAP q a X : ℕ) : ℝ) * Real.log B :=
    lt_of_lt_of_le (by linarith) (primeCountAP_diff_mul_log_ge q a hX hXB)
  have hcnt_pos : 0 < primeCountAP q a B - primeCountAP q a X := by
    by_contra h0
    have hzero : primeCountAP q a B - primeCountAP q a X = 0 := by omega
    rw [hzero, Nat.cast_zero, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have hfl : ⌊X⌋₊ + 1 ≤ ⌊B⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono hXB) 1
  have hsub_range : Finset.range (⌊X⌋₊ + 1) ⊆ Finset.range (⌊B⌋₊ + 1) := Finset.range_mono hfl
  have hsub_filt :
      (Finset.range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
        (Finset.range (⌊B⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) :=
    Finset.filter_subset_filter _ hsub_range
  have hsdiff_pos :
      0 < (((Finset.range (⌊B⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])) \
            ((Finset.range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]))).card := by
    rwa [Finset.card_sdiff_of_subset hsub_filt]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hsdiff_pos
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨⟨hpB, hpr, hmod⟩, hnot⟩ := hp
  have hp_gt_fl : ⌊X⌋₊ < p := by
    by_contra hle
    exact hnot ⟨by omega, hpr, hmod⟩
  refine ⟨p, hpr, hmod, ?_, ?_⟩
  · exact (Nat.floor_lt (by linarith)).mp hp_gt_fl
  · exact le_trans (by exact_mod_cast (by omega : p ≤ ⌊B⌋₊)) (Nat.floor_le (by linarith))

/-- **Quantitative Least-Prime-in-AP Bound**:
if `1 ≤ B` and `√B * log B < ψ(B; q, a)`, then there exists a prime `p ≡ a [MOD q]` with `p ≤ B`. -/
theorem exists_prime_le_of_psiAP_gt (q a : ℕ) {B : ℝ} (hB : 1 ≤ B)
    (hgt : Real.sqrt B * Real.log B < chebyshevPsiAP q a B) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ B := by
  have hdiff : Real.sqrt B * Real.log B < chebyshevPsiAP q a B - chebyshevPsiAP q a 1 := by
    rw [chebyshevPsiAP_one, sub_zero]
    exact hgt
  obtain ⟨p, hp, hmod, _, hpB⟩ := exists_prime_in_Ioc_of_psiAP_diff_gt q a le_rfl hB hdiff
  exact ⟨p, hp, hmod, hpB⟩

/-! ## Section 5: Direct Quantitative Reduction to `Stage2PrimePairs`'s Linnik Hypotheses -/

/-- **Quantitative Relative PNT-in-AP Bound (`PsiAPRelativeBound`)**:
there exists `L ≥ 1` such that for all `q ≥ 2`, `Nat.Coprime a q`, and `x ≥ q ^ L`,
`|ψ(x; q, a) - x / φ(q)| ≤ x / (4 * φ(q))`. -/
def PsiAPRelativeBound : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∀ (q a : ℕ), 2 ≤ q → Nat.Coprime a q →
    ∀ x : ℝ, (q : ℝ) ^ L ≤ x →
      |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ x / (4 * (q.totient : ℝ))

/-- **Uniform Power-Saving Character-Sum Bound (`PsiCharPowerBound θ`)**:
the direct analytic output of a zero-free strip `Re(s) > θ` (with `θ < 1`, e.g. GRH at
any `θ ∈ (1/2, 1)`): `|ψ(x) - x| ≤ C x^θ` and `‖ψ(x, χ)‖ ≤ C (log q + 1) x^θ` for all
non-principal `χ mod q` and `x ≥ 2`. -/
def PsiCharPowerBound (θ : ℝ) : Prop :=
  0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ x : ℝ, 2 ≤ x →
      |chebyshevPsi x - x| ≤ C * x ^ θ ∧
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ‖chebyshevPsiChar χ x‖ ≤ C * (Real.log (q : ℝ) + 1) * x ^ θ

private lemma sqrt_two_mul_log_lt_div_four_q {q : ℕ} (hq : 2 ≤ q) {X : ℝ}
    (hX : (q : ℝ) ^ (25 : ℝ) ≤ X) :
    Real.sqrt (2 * X) * Real.log (2 * X) < X / (4 * (q : ℝ)) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hX_ge_q25 : (q : ℝ) ^ (25 : ℕ) ≤ X := by
    rwa [← Real.rpow_natCast]
  have hXpos : 0 < X := lt_of_lt_of_le (pow_pos hqpos 25) hX_ge_q25
  have h2Xpos : 0 < 2 * X := by linarith
  -- Bound `log(2X) ≤ 4 * (2X)^(1/4)` via `Real.log_le_rpow_div`.
  have hlog : Real.log (2 * X) ≤ 4 * (2 * X) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div h2Xpos.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hsqrt : Real.sqrt (2 * X) = (2 * X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (2 * X)
  have hprod : Real.sqrt (2 * X) * Real.log (2 * X) ≤ 4 * (2 * X) ^ ((3 : ℝ) / 4) := by
    rw [hsqrt]
    calc (2 * X) ^ ((1 : ℝ) / 2) * Real.log (2 * X)
        ≤ (2 * X) ^ ((1 : ℝ) / 2) * (4 * (2 * X) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg h2Xpos.le _)
      _ = 4 * ((2 * X) ^ ((1 : ℝ) / 2) * (2 * X) ^ ((1 : ℝ) / 4)) := by ring
      _ = 4 * (2 * X) ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_add h2Xpos]
          norm_num
  have h2_34 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hbound : 4 * (2 * X) ^ ((3 : ℝ) / 4) ≤ 8 * X ^ ((3 : ℝ) / 4) := by
    rw [Real.mul_rpow (by norm_num) hXpos.le]
    nlinarith [Real.rpow_nonneg hXpos.le ((3 : ℝ) / 4)]
  -- Show `32 * q < X ^ (1/4)`, equivalently `(32 * q)^4 < X`.
  have h32q : 32 * (q : ℝ) < X ^ ((1 : ℝ) / 4) := by
    have hpow4 : (32 * (q : ℝ)) ^ 4 < X := by
      have hq21 : (2 : ℝ) ^ 21 ≤ (q : ℝ) ^ 21 := pow_le_pow_left₀ (by norm_num) hqR 21
      have h32_4 : (32 : ℝ) ^ 4 < (2 : ℝ) ^ 21 := by norm_num
      have hq25 : (q : ℝ) ^ 25 = (q : ℝ) ^ 4 * (q : ℝ) ^ 21 := by ring
      calc (32 * (q : ℝ)) ^ 4 = (q : ℝ) ^ 4 * (32 : ℝ) ^ 4 := by ring
        _ < (q : ℝ) ^ 4 * (2 : ℝ) ^ 21 :=
            mul_lt_mul_of_pos_left h32_4 (pow_pos hqpos 4)
        _ ≤ (q : ℝ) ^ 4 * (q : ℝ) ^ 21 :=
            mul_le_mul_of_nonneg_left hq21 (pow_nonneg hqpos.le 4)
        _ = (q : ℝ) ^ 25 := hq25.symm
        _ ≤ X := hX_ge_q25
    have hpow4_rpow : (32 * (q : ℝ)) ^ (4 : ℝ) < X := by
      rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hrpow : ((32 * (q : ℝ)) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) < X ^ ((1 : ℝ) / 4) :=
      Real.rpow_lt_rpow (by positivity) hpow4_rpow (by norm_num)
    have hlhs : ((32 * (q : ℝ)) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = 32 * (q : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    rwa [hlhs] at hrpow
  have hX34_pos : 0 < X ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hXpos _
  have hmul_lt : 8 * X ^ ((3 : ℝ) / 4) * (4 * (q : ℝ)) < X := by
    have h1 : 8 * X ^ ((3 : ℝ) / 4) * (4 * (q : ℝ)) = X ^ ((3 : ℝ) / 4) * (32 * (q : ℝ)) := by ring
    rw [h1]
    calc X ^ ((3 : ℝ) / 4) * (32 * (q : ℝ))
        < X ^ ((3 : ℝ) / 4) * X ^ ((1 : ℝ) / 4) := mul_lt_mul_of_pos_left h32q hX34_pos
      _ = X ^ ((3 : ℝ) / 4 + (1 : ℝ) / 4) := (Real.rpow_add hXpos _ _).symm
      _ = X := by norm_num
  have hdiv_lt : 8 * X ^ ((3 : ℝ) / 4) < X / (4 * (q : ℝ)) :=
    (lt_div_iff₀ (by positivity)).mpr hmul_lt
  exact lt_of_le_of_lt (hprod.trans hbound) hdiv_lt

/-- **Master Quantitative Bridge (`PsiAPRelativeBound → Stage2PrimePairs.LinnikAPDyadic`)**:
any relative PNT-in-AP bound `|ψ(x; q, a) - x / φ(q)| ≤ x / (4 φ(q))` for `x ≥ q^L`
directly proves `Stage2PrimePairs.LinnikAPDyadic` (a prime `p ≡ a [MOD q]` in `(X, 2X]`
for every `X ≥ q ^ max L 25`). -/
theorem linnikAPDyadic_of_psiAPRelativeBound (hPsi : PsiAPRelativeBound) :
    Stage2PrimePairs.LinnikAPDyadic := by
  obtain ⟨L, hL1, hL⟩ := hPsi
  refine ⟨max L 25, le_trans hL1 (le_max_left _ _), fun q a hq hcop X hX => ?_⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hX_L : (q : ℝ) ^ L ≤ X :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hq1 (le_max_left L 25)) hX
  have hX_25 : (q : ℝ) ^ (25 : ℝ) ≤ X :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hq1 (le_max_right L 25)) hX
  have hX1 : 1 ≤ X := by
    have hq25 : (1 : ℝ) ≤ (q : ℝ) ^ (25 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
    exact hq25.trans hX_25
  have h2X_L : (q : ℝ) ^ L ≤ 2 * X := by linarith
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hphi_le : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hlo_2X := (abs_le.mp (hL q a hq hcop (2 * X) h2X_L)).1
  have hhi_X := (abs_le.mp (hL q a hq hcop X hX_L)).2
  have hdiff_ge : X / (4 * (q.totient : ℝ)) ≤ chebyshevPsiAP q a (2 * X) - chebyshevPsiAP q a X := by
    have hA : 2 * X / (q.totient : ℝ) - 2 * X / (4 * (q.totient : ℝ)) ≤ chebyshevPsiAP q a (2 * X) := by
      linarith
    have hB : chebyshevPsiAP q a X ≤ X / (q.totient : ℝ) + X / (4 * (q.totient : ℝ)) := by
      linarith
    have halg :
        (2 * X / (q.totient : ℝ) - 2 * X / (4 * (q.totient : ℝ))) -
          (X / (q.totient : ℝ) + X / (4 * (q.totient : ℝ))) =
        X / (4 * (q.totient : ℝ)) := by
      field_simp [hphi_pos.ne']
      ring
    linarith
  have hcmp : X / (4 * (q : ℝ)) ≤ X / (4 * (q.totient : ℝ)) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  have hgt : Real.sqrt (2 * X) * Real.log (2 * X) <
      chebyshevPsiAP q a (2 * X) - chebyshevPsiAP q a X :=
    lt_of_lt_of_le (sqrt_two_mul_log_lt_div_four_q hq hX_25) (hcmp.trans hdiff_ge)
  exact exists_prime_in_Ioc_of_psiAP_diff_gt q a hX1 (by linarith) hgt

/-- `PsiAPRelativeBound` directly discharges `Stage2PrimePairs.LinnikAPInterval`. -/
theorem linnikAPInterval_of_psiAPRelativeBound (hPsi : PsiAPRelativeBound) :
    Stage2PrimePairs.LinnikAPInterval :=
  Stage2PrimePairs.linnikAPInterval_of_dyadic (linnikAPDyadic_of_psiAPRelativeBound hPsi)

/-- `PsiAPRelativeBound` directly discharges `HostFieldSupply.PairSupply`. -/
theorem pairSupply_of_psiAPRelativeBound (hPsi : PsiAPRelativeBound) :
    HostFieldSupply.PairSupply :=
  Stage2PrimePairs.pairSupply_of_linnikAPDyadic (linnikAPDyadic_of_psiAPRelativeBound hPsi)

/-- `PsiAPRelativeBound` directly discharges `ThetaSlopeEngine.PairEx`. -/
theorem pairEx_of_psiAPRelativeBound (hPsi : PsiAPRelativeBound) :
    ThetaSlopeEngine.PairEx :=
  Stage2PrimePairs.pairEx_of_linnikAPDyadic (linnikAPDyadic_of_psiAPRelativeBound hPsi)

/-- `PsiAPRelativeBound` directly discharges `HostFieldSupply.SmallOne`. -/
theorem smallOne_of_psiAPRelativeBound (hPsi : PsiAPRelativeBound) :
    HostFieldSupply.SmallOne :=
  Stage2PrimePairs.smallOne_of_linnikAPInterval (linnikAPInterval_of_psiAPRelativeBound hPsi)

private lemma nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := n))

/-- **Zero-Free / Power-Saving Character-Sum Reduction (`PsiCharPowerBound θ → PsiAPRelativeBound`)**:
any uniform power-saving bound `|ψ(x) - x| ≤ C x^θ` and `‖ψ(x, χ)‖ ≤ C (log q + 1) x^θ`
with `θ < 1` automatically implies `PsiAPRelativeBound` with an explicit Linnik exponent `L`. -/
theorem psiAPRelativeBound_of_psiCharPowerBound {θ : ℝ} (h : PsiCharPowerBound θ) :
    PsiAPRelativeBound := by
  obtain ⟨hθ0, hθ1, C, hC0, hC⟩ := h
  set δ : ℝ := 1 - θ
  have hδ : 0 < δ := by linarith
  set K : ℕ := ⌈24 * C + 48⌉₊
  have hK_ge : 24 * C + 48 ≤ (K : ℝ) := Nat.le_ceil _
  set L : ℝ := max 12 (((K : ℝ) + 4) / δ)
  have hL1 : 1 ≤ L := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨L, hL1, fun q a hq hcop x hx => ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hphi_le : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hx_12 : (q : ℝ) ^ (12 : ℝ) ≤ x :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hq1 (le_max_left _ _)) hx
  have hx_K : (q : ℝ) ^ (((K : ℝ) + 4) / δ) ≤ x :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hq1 (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := by
    have hq12 : (2 : ℝ) ≤ (q : ℝ) ^ (12 : ℝ) := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hqR (by norm_num)
        _ ≤ (q : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    exact hq12.trans hx_12
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  obtain ⟨hpsi_err, hchar_err⟩ := hC q hq x hx2
  have hE₂_nn : 0 ≤ C * (Real.log (q : ℝ) + 1) * x ^ θ :=
    mul_nonneg (mul_nonneg hC0 (by linarith [Real.log_nonneg hq1])) (Real.rpow_nonneg hxpos.le _)
  have htri := abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop hx1 hE₂_nn hpsi_err hchar_err
  -- Lower bound `x ^ δ ≥ q ^ (K + 4) = q^4 * q^K ≥ q^4 * 2^K ≥ K * q^4`.
  have hx_delta : (K : ℝ) * (q : ℝ) ^ 4 ≤ x ^ δ := by
    have h1 : ((q : ℝ) ^ (((K : ℝ) + 4) / δ)) ^ δ ≤ x ^ δ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hqpos.le _) hx_K hδ.le
    have h2 : ((q : ℝ) ^ (((K : ℝ) + 4) / δ)) ^ δ = (q : ℝ) ^ ((K : ℝ) + 4) := by
      rw [← Real.rpow_mul hqpos.le]
      congr 1
      field_simp [hδ.ne']
    rw [h2] at h1
    have h3 : (q : ℝ) ^ ((K : ℝ) + 4) = (q : ℝ) ^ K * (q : ℝ) ^ 4 := by
      rw [Real.rpow_add hqpos, Real.rpow_natCast]
      norm_num
    rw [h3] at h1
    have h2K : (K : ℝ) ≤ (q : ℝ) ^ K :=
      (nat_le_two_pow K).trans (pow_le_pow_left₀ (by norm_num) hqR K)
    exact (mul_le_mul_of_nonneg_right h2K (pow_nonneg hqpos.le 4)).trans h1
  -- Term 1: `C * x^θ ≤ x / 12`.
  have hterm1 : C * x ^ θ ≤ x / 12 := by
    have h12C : 12 * C ≤ x ^ δ := by
      have hq4 : (1 : ℝ) ≤ (q : ℝ) ^ 4 := one_le_pow₀ hq1
      have hK12 : 12 * C ≤ (K : ℝ) := by linarith
      nlinarith
    have hmul : 12 * C * x ^ θ ≤ x ^ δ * x ^ θ :=
      mul_le_mul_of_nonneg_right h12C (Real.rpow_nonneg hxpos.le _)
    have hadd : x ^ δ * x ^ θ = x := by
      rw [← Real.rpow_add hxpos]
      have : δ + θ = 1 := by dsimp only [δ]; ring
      rw [this, Real.rpow_one]
    linarith
  -- Term 2: `ω(q) * log x ≤ x / 12`.
  have hterm2 : (q.primeFactors.card : ℝ) * Real.log x ≤ x / 12 := by
    have homega : (q.primeFactors.card : ℝ) ≤ (q : ℝ) := by
      have hnat : q.primeFactors.card ≤ q :=
        (Nat.le_of_lt Nat.lt_two_pow_self).trans (two_pow_card_primeFactors_le (by omega))
      exact_mod_cast hnat
    have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
      have h := Real.log_le_rpow_div hxpos.le (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have h24q : 24 * (q : ℝ) ≤ Real.sqrt x := by
      have hsq : (24 * (q : ℝ)) ^ 2 ≤ x := by
        have hq10 : (2 : ℝ) ^ 10 ≤ (q : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hqR 10
        have h24_2 : (24 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 10 := by norm_num
        have hq12 : (q : ℝ) ^ (12 : ℕ) ≤ x := by rwa [← Real.rpow_natCast]
        have hfact : (q : ℝ) ^ (12 : ℕ) = (q : ℝ) ^ 2 * (q : ℝ) ^ 10 := by ring
        calc (24 * (q : ℝ)) ^ 2 = (q : ℝ) ^ 2 * (24 : ℝ) ^ 2 := by ring
          _ ≤ (q : ℝ) ^ 2 * (2 : ℝ) ^ 10 :=
              mul_le_mul_of_nonneg_left h24_2 (pow_nonneg hqpos.le 2)
          _ ≤ (q : ℝ) ^ 2 * (q : ℝ) ^ 10 :=
              mul_le_mul_of_nonneg_left hq10 (pow_nonneg hqpos.le 2)
          _ = (q : ℝ) ^ (12 : ℕ) := hfact.symm
          _ ≤ x := hq12
      exact Real.le_sqrt_of_sq_le hsq
    have hmul_sq : 12 * ((q.primeFactors.card : ℝ) * Real.log x) ≤ x := by
      calc 12 * ((q.primeFactors.card : ℝ) * Real.log x)
          ≤ 12 * ((q : ℝ) * (2 * Real.sqrt x)) := by
            have h1 := mul_le_mul homega hlogx (Real.log_nonneg hx1) hqpos.le
            linarith
        _ = (24 * (q : ℝ)) * Real.sqrt x := by ring
        _ ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_right h24q (Real.sqrt_nonneg x)
        _ = x := Real.mul_self_sqrt hxpos.le
    linarith
  -- Term 3: `C * (log q + 1) * x^θ ≤ x / (12 * φ(q))`.
  have hterm3 : C * (Real.log (q : ℝ) + 1) * x ^ θ ≤ x / (12 * (q.totient : ℝ)) := by
    have hlogq : Real.log (q : ℝ) + 1 ≤ (q : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos hqpos
      linarith
    have hq_sq : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 4 := by
      have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hq1
      nlinarith [sq_nonneg (q : ℝ)]
    have h12_bound : 12 * (q.totient : ℝ) * (C * (Real.log (q : ℝ) + 1)) ≤ x ^ δ := by
      calc 12 * (q.totient : ℝ) * (C * (Real.log (q : ℝ) + 1))
          ≤ 12 * (q : ℝ) * (C * (q : ℝ)) := by
            have hA : 12 * (q.totient : ℝ) ≤ 12 * (q : ℝ) := by linarith
            have hB : C * (Real.log (q : ℝ) + 1) ≤ C * (q : ℝ) :=
              mul_le_mul_of_nonneg_left hlogq hC0
            exact mul_le_mul hA hB
              (mul_nonneg hC0 (by linarith [Real.log_nonneg hq1])) (by positivity)
        _ = (12 * C) * (q : ℝ) ^ 2 := by ring
        _ ≤ (K : ℝ) * (q : ℝ) ^ 4 :=
            mul_le_mul (by linarith) hq_sq (sq_nonneg _) (by positivity)
        _ ≤ x ^ δ := hx_delta
    have hmul : 12 * (q.totient : ℝ) * (C * (Real.log (q : ℝ) + 1) * x ^ θ) ≤ x := by
      have hadd : x ^ δ * x ^ θ = x := by
        rw [← Real.rpow_add hxpos]
        have : δ + θ = 1 := by dsimp only [δ]; ring
        rw [this, Real.rpow_one]
      calc 12 * (q.totient : ℝ) * (C * (Real.log (q : ℝ) + 1) * x ^ θ)
          = (12 * (q.totient : ℝ) * (C * (Real.log (q : ℝ) + 1))) * x ^ θ := by ring
        _ ≤ x ^ δ * x ^ θ := mul_le_mul_of_nonneg_right h12_bound (Real.rpow_nonneg hxpos.le _)
        _ = x := hadd
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  -- Combine all three terms: `(x/12 + x/12) / φ(q) + x / (12 φ(q)) = x / (4 φ(q))`.
  have hsum_bound :
      (C * x ^ θ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) +
        C * (Real.log (q : ℝ) + 1) * x ^ θ ≤ x / (4 * (q.totient : ℝ)) := by
    have h12 :
        (C * x ^ θ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
          (x / 12 + x / 12) / (q.totient : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hphi_pos.le
    have halg : (x / 12 + x / 12) / (q.totient : ℝ) + x / (12 * (q.totient : ℝ)) =
        x / (4 * (q.totient : ℝ)) := by
      field_simp [hphi_pos.ne']
      ring
    linarith
  exact htri.trans hsum_bound

/-- **End-to-End Zero-Free / Power-Saving Bridge to `Stage2PrimePairs`**:
any uniform power-saving character-sum bound `PsiCharPowerBound θ` (`θ < 1`) directly
discharges `LinnikAPDyadic`, `LinnikAPInterval`, `HostFieldSupply.PairSupply`,
`ThetaSlopeEngine.PairEx`, and `HostFieldSupply.SmallOne` in one shot. -/
theorem stage2PrimePairs_of_psiCharPowerBound {θ : ℝ} (h : PsiCharPowerBound θ) :
    Stage2PrimePairs.LinnikAPDyadic ∧
      Stage2PrimePairs.LinnikAPInterval ∧
      HostFieldSupply.PairSupply ∧
      ThetaSlopeEngine.PairEx ∧
      HostFieldSupply.SmallOne := by
  have hrel := psiAPRelativeBound_of_psiCharPowerBound h
  exact ⟨linnikAPDyadic_of_psiAPRelativeBound hrel,
    linnikAPInterval_of_psiAPRelativeBound hrel,
    pairSupply_of_psiAPRelativeBound hrel,
    pairEx_of_psiAPRelativeBound hrel,
    smallOne_of_psiAPRelativeBound hrel⟩

end RHDirect.Stage2DirichletAP

end
