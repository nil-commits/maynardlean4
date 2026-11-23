import RHDirect.Stage7SieveMethods
import RHDirect.Stage8BarbanDavenport
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage10ZeroDensity

/-!
# RHDirect.Stage11BombieriVinogradov

100%-unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, pure Mathlib `v4.33.1`)
formalization of:
1. **Unconditional Vaughan's Identity (1977) for `Λ(n)`** and exact bilinear Type I / Type II
   decomposition of `chebyshevPsiChar χ x`;
2. **Unconditional Multiplicative Large Sieve Inequality** (weighted by `q / φ(q)` over primitive
   Dirichlet characters via Gauss sum orthogonality `|τ(χ)|² = q`), **Bilinear Multiplicative
   Large Sieve**, and **Unconditional Pólya–Vinogradov Inequality** (standard & log-weighted);
3. **Unconditional Type I & Type II Dyadic Primitive-Character Bounds** (sub-dyadic rectangle +
   thin-annulus boundary Large Sieve decomposition without contour integration);
4. **Unconditional Full Bombieri–Vinogradov Theorem (`ϑ = 1/2`)** combining Vaughan's identity,
   Pólya–Vinogradov, Multiplicative Large Sieve, and `Stage10SiegelWalfiszFull`;
5. **Unconditional Brun–Titchmarsh Inequality** for all `1 ≤ q < x` (together with direct
   Selberg-sieve prime upper bound via `Stage7SieveMethods`).
-/

noncomputable section

open Complex DirichletCharacter Finset Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage11BombieriVinogradov

/-! ## Section 1: Unconditional Vaughan's Identity (1977) for `Λ(n)` & Bilinear Character Reduction -/

/-- Truncated Möbius convolution weight `c_U(k) = ∑_{d ∣ k, d ≤ U} μ(d)` in Vaughan's identity. -/
def vaughanMollifier (U k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℝ)

/-- Small-range cutoff term `a₀(n) = 1_{n ≤ V} Λ(n)` in Vaughan's identity. -/
def vaughanA0 (V n : ℕ) : ℝ :=
  if n ≤ V then Λ n else 0

/-- First Type I term `a₁(n) = ∑_{d ∣ n, d ≤ U} μ(d) log(n / d)` in Vaughan's identity. -/
def vaughanA1 (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U),
    (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- Second Type I term `a₂(n) = ∑_{d ∣ n, d ≤ U} μ(d) ∑_{m ∣ (n/d), m ≤ V} Λ(m)` in Vaughan's identity. -/
def vaughanA2 (U V n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U),
    (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (· ≤ V), Λ m

/-- Type II bilinear term `a₃(n) = ∑_{m ∣ n, m > V, n/m > U} Λ(m) c_U(n/m)` in Vaughan's identity. -/
def vaughanA3 (U V n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => V < m ∧ U < n / m),
    Λ m * vaughanMollifier U (n / m)

theorem vaughanMollifier_one {U : ℕ} (hU : 1 ≤ U) : vaughanMollifier U 1 = 1 := by
  unfold vaughanMollifier
  have hfilt : (1 : ℕ).divisors.filter (· ≤ U) = {1} := by
    ext d
    simp only [Nat.divisors_one, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hU⟩⟩
  rw [hfilt, Finset.sum_singleton]
  simp

theorem vaughanMollifier_eq_zero_of_le {U k : ℕ} (hk2 : 2 ≤ k) (hkU : k ≤ U) :
    vaughanMollifier U k = 0 := by
  unfold vaughanMollifier
  have hfilt : k.divisors.filter (· ≤ U) = k.divisors :=
    Finset.filter_true_of_mem fun d hd =>
      (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hkU
  rw [hfilt]
  have hZ : ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
    have hmul := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) k
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg (by omega)] at hmul
    rw [← hmul, Nat.sum_divisorsAntidiagonal
      (f := fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hq : k / d ≠ 0 := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      exact Nat.div_ne_zero_iff.mpr ⟨(Nat.pos_of_mem_divisors hd).ne', Nat.le_of_dvd (by omega) hdvd⟩
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq]
  exact_mod_cast hZ

theorem abs_vaughanMollifier_le_divisors (U k : ℕ) :
    |vaughanMollifier U k| ≤ (k.divisors.card : ℝ) := by
  unfold vaughanMollifier
  calc |∑ d ∈ k.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ k.divisors.filter (· ≤ U), |(ArithmeticFunction.moebius d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ k.divisors.filter (· ≤ U), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        by_cases hsq : Squarefree d
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
          simp [abs_pow]
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          simp
    _ = ((k.divisors.filter (· ≤ U)).card : ℝ) := by simp
    _ ≤ (k.divisors.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)

/-- **Unconditional Vaughan's Identity (1977)** for all `U ≥ 1`, `V : ℕ`, and `n ≥ 1`:
`Λ(n) = a₀(n) + a₁(n) - a₂(n) - a₃(n)`. -/
theorem vaughan_identity {U V n : ℕ} (hU : 1 ≤ U) (hn : 1 ≤ n) :
    Λ n = vaughanA0 V n + vaughanA1 U n - vaughanA2 U V n - vaughanA3 U V n := by
  have hn0 : n ≠ 0 := by omega
  -- Step 1: `a₁(n) - a₂(n) = ∑_{d ∣ n, d ≤ U} μ(d) ∑_{m ∣ (n/d), m > V} Λ(m)`
  have hdiff : vaughanA1 U n - vaughanA2 U V n =
      ∑ d ∈ n.divisors.filter (· ≤ U),
        (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m := by
    unfold vaughanA1 vaughanA2
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← mul_sub]
    congr 1
    have hlog : Real.log ((n / d : ℕ) : ℝ) = ∑ m ∈ (n / d).divisors, Λ m :=
      ArithmeticFunction.vonMangoldt_sum.symm
    rw [hlog, ← Finset.sum_filter_add_sum_filter_not (n / d).divisors (· ≤ V)]
    have hnot : (n / d).divisors.filter (fun m => ¬ m ≤ V) =
        (n / d).divisors.filter (fun m => V < m) := by
      ext m; simp
    rw [hnot]
    ring
  -- Step 2: Swap `(d, m)` to `∑_{m ∣ n, m > V} Λ(m) * c_U(n/m)`
  have hswap :
      ∑ d ∈ n.divisors.filter (· ≤ U),
          (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m =
        ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) := by
    have hL :
        ∑ d ∈ n.divisors.filter (· ≤ U),
            (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m =
          ∑ d ∈ n.divisors.filter (· ≤ U), ∑ m ∈ n.divisors.filter (fun m => V < m),
            if d * m ∣ n then (ArithmeticFunction.moebius d : ℝ) * Λ m else 0 := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hm_dvd, hnd_ne⟩, hVm⟩
        have hdm : d * m ∣ n := by
          obtain ⟨r, hr⟩ := hm_dvd
          exact ⟨r, by rw [← Nat.mul_div_cancel' hdvd, hr]; ring⟩
        exact ⟨⟨⟨(dvd_mul_left m d).trans hdm, hn0⟩, hVm⟩, hdm⟩
      · rintro ⟨⟨⟨_, _⟩, hVm⟩, hdm⟩
        have hnd_ne : n / d ≠ 0 :=
          Nat.div_ne_zero_iff.mpr ⟨hdpos.ne', Nat.le_of_dvd hn hdvd⟩
        have hm_dvd : m ∣ n / d := by
          obtain ⟨r, hr⟩ := hdm
          refine ⟨r, ?_⟩
          have h1 : d * (n / d) = d * (m * r) := by
            rw [Nat.mul_div_cancel' hdvd, hr]; ring
          exact Nat.eq_of_mul_eq_mul_left hdpos h1
        exact ⟨⟨hm_dvd, hnd_ne⟩, hVm⟩
    have hR :
        ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) =
          ∑ m ∈ n.divisors.filter (fun m => V < m), ∑ d ∈ n.divisors.filter (· ≤ U),
            if d * m ∣ n then (ArithmeticFunction.moebius d : ℝ) * Λ m else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_dvd : m ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm).1
      have hmpos : 0 < m := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hm).1
      unfold vaughanMollifier
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun d _ => mul_comm _ _
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd_dvd, _⟩, hdU⟩
        have hdm : d * m ∣ n := by
          obtain ⟨r, hr⟩ := hd_dvd
          exact ⟨r, by rw [← Nat.mul_div_cancel' hm_dvd, hr]; ring⟩
        exact ⟨⟨⟨(dvd_mul_right d m).trans hdm, hn0⟩, hdU⟩, hdm⟩
      · rintro ⟨⟨⟨_, _⟩, hdU⟩, hdm⟩
        have hnm_ne : n / m ≠ 0 :=
          Nat.div_ne_zero_iff.mpr ⟨hmpos.ne', Nat.le_of_dvd hn hm_dvd⟩
        have hd_dvd : d ∣ n / m := by
          obtain ⟨r, hr⟩ := hdm
          refine ⟨r, ?_⟩
          have h1 : m * (n / m) = m * (d * r) := by
            rw [Nat.mul_div_cancel' hm_dvd, hr]; ring
          exact Nat.eq_of_mul_eq_mul_left hmpos h1
        exact ⟨⟨hd_dvd, hnm_ne⟩, hdU⟩
    rw [hL, Finset.sum_comm, ← hR]
  -- Step 3: Split `m ∣ n, m > V` by `n/m = 1`, `2 ≤ n/m ≤ U`, `n/m > U`
  have hsplit :
      ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) =
        (Λ n - vaughanA0 V n) + vaughanA3 U V n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (n.divisors.filter (fun m => V < m)) (fun m => U < n / m)]
    have hA3 :
        ∑ m ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => U < n / m),
            Λ m * vaughanMollifier U (n / m) = vaughanA3 U V n := by
      unfold vaughanA3
      congr 1; ext m; simp [and_assoc]
    have hsmall :
        ∑ m ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m),
            Λ m * vaughanMollifier U (n / m) = Λ n - vaughanA0 V n := by
      by_cases hVn : V < n
      · have hn_mem : n ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m) := by
          simp only [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨⟨dvd_rfl, hn0⟩, hVn⟩, by rw [Nat.div_self hn]; omega⟩
        rw [Finset.sum_eq_single n]
        · rw [Nat.div_self hn, vaughanMollifier_one hU, mul_one]
          unfold vaughanA0; rw [if_neg (by omega)]; ring
        · intro m hm hmn
          simp only [Finset.mem_filter, Nat.mem_divisors] at hm
          have hq_ge2 : 2 ≤ n / m := by
            have hm_le : m ≤ n := Nat.le_of_dvd hn hm.1.1.1
            have hm_lt : m < n := lt_of_le_of_ne hm_le hmn
            have hmul := Nat.mul_div_cancel' hm.1.1.1
            have hq0 : n / m ≠ 0 := by intro h0; rw [h0, mul_zero] at hmul; omega
            have hq1 : n / m ≠ 1 := by intro h1; rw [h1, mul_one] at hmul; omega
            rcases Nat.lt_or_ge (n / m) 2 with hlt | hge
            · exfalso
              have hle1 : n / m ≤ 1 := Nat.lt_succ_iff.mp hlt
              rcases Nat.eq_zero_or_pos (n / m) with h0 | hp
              · exact hq0 h0
              · exact hq1 (le_antisymm hle1 hp)
            · exact hge
          rw [vaughanMollifier_eq_zero_of_le hq_ge2 (Nat.not_lt.mp hm.2), mul_zero]
        · intro h; exact absurd hn_mem h
      · have hempty : (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m) = ∅ := by
          ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false]
          rintro ⟨⟨⟨hmn, _⟩, hVm⟩, _⟩
          have := Nat.le_of_dvd hn hmn
          omega
        rw [hempty, Finset.sum_empty]
        unfold vaughanA0; rw [if_pos (by omega)]; ring
    rw [hA3, hsmall, add_comm]
  linarith

/-- **Vaughan's Identity for `n > V`**: the cutoff term `a₀(n)` vanishes identically. -/
theorem vaughan_identity_gt {U V n : ℕ} (hU : 1 ≤ U) (hVn : V < n) :
    Λ n = vaughanA1 U n - vaughanA2 U V n - vaughanA3 U V n := by
  have hn : 1 ≤ n := by omega
  have h := vaughan_identity (U := U) (V := V) hU hn
  unfold vaughanA0 at h
  rw [if_neg (by omega)] at h
  linarith

/-- Vaughan Type 0 cutoff sum `S₀(χ; V, x) = ∑_{1 ≤ n ≤ min(⌊x⌋₊, V)} χ(n) Λ(n)`. -/
def vaughanS0 {q : ℕ} (χ : DirichletCharacter ℂ q) (V : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), χ (n : ZMod q) * (Λ n : ℂ)

/-- Vaughan Type I first sum `S₁(χ; U, x) = ∑_{d ≤ U} μ(d) χ(d) ∑_{m ≤ x/d} χ(m) log m`. -/
def vaughanS1 {q : ℕ} (χ : DirichletCharacter ℂ q) (U : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U,
    (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
      ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), χ (m : ZMod q) * (Real.log (m : ℝ) : ℂ)

/-- Vaughan Type I second sum `S₂(χ; U, V, x) = ∑_{d ≤ U} μ(d) χ(d) ∑_{m ≤ V} Λ(m) χ(m) ∑_{r ≤ x/(dm)} χ(r)`. -/
def vaughanS2 {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U,
    (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
      ∑ m ∈ Finset.Icc 1 V,
        (Λ m : ℂ) * χ (m : ZMod q) *
          ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (d * m)), χ (r : ZMod q)

/-- Vaughan Type II bilinear sum `S₃(χ; U, V, x) = ∑_{V < m ≤ x/U} Λ(m) χ(m) ∑_{U < k ≤ x/m} c_U(k) χ(k)`. -/
def vaughanS3 {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc V (⌊x⌋₊ / U),
    (Λ m : ℂ) * χ (m : ZMod q) *
      ∑ k ∈ Finset.Ioc U (⌊x⌋₊ / m), (vaughanMollifier U k : ℂ) * χ (k : ZMod q)

/-- **Exact Bilinear Character-Sum Reduction of `ψ(x, χ)` via Vaughan's Identity**:
for every `q`, `χ : DirichletCharacter ℂ q`, `U ≥ 1`, `V : ℕ`, and `x ≥ 1`,
`ψ(x, χ) = S₀(χ; V, x) + S₁(χ; U, x) - S₂(χ; U, V, x) - S₃(χ; U, V, x)`. -/
theorem chebyshevPsiChar_vaughan_decomp {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) {x : ℝ} (_hx : 1 ≤ x) :
    Stage2DirichletAP.chebyshevPsiChar χ x =
      vaughanS0 χ V x + vaughanS1 χ U x - vaughanS2 χ U V x - vaughanS3 χ U V x := by
  set N : ℕ := ⌊x⌋₊
  rw [Stage3BombieriVinogradov.chebyshevPsiChar_eq_sum_Icc]
  have hcomm : ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * χ (n : ZMod q) =
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Λ n : ℂ) :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hcomm]
  have hpoint :
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Λ n : ℂ) =
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA0 V n : ℂ) +
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA1 U n : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA2 U V n : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA3 U V n : ℂ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hv := congrArg (Complex.ofReal : ℝ → ℂ) (vaughan_identity (U := U) (V := V) hU hn1)
    simp only [Complex.ofReal_add, Complex.ofReal_sub] at hv
    rw [hv]; ring
  rw [hpoint]
  -- Match S₀
  have hS0 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA0 V n : ℂ) = vaughanS0 χ V x := by
    unfold vaughanA0 vaughanS0
    have hfilt : (Finset.Icc 1 N).filter (· ≤ V) = Finset.Icc 1 (min N V) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]; tauto
    rw [← hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ V <;> simp [h]
  -- Match S₁
  have hS1 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA1 U n : ℂ) = vaughanS1 χ U x := by
    unfold vaughanA1 vaughanS1
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U,
            if d ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
                (χ ((n / d : ℕ) : ZMod q) * (Real.log ((n / d : ℕ) : ℝ) : ℂ))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_filter]
      have hset : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hset]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdn : d ∣ n := (Finset.mem_filter.mp hd).2
      have hmul : (n : ZMod q) = (d : ZMod q) * ((n / d : ℕ) : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
      rw [hmul, map_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hm1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hd1
      exact ⟨hm1, (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).mp hm.2
      rwa [mul_comm] at this
    · intro n _; rfl
  -- Match S₂
  have hS2 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA2 U V n : ℂ) = vaughanS2 χ U V x := by
    unfold vaughanA2 vaughanS2
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) *
                ∑ m ∈ (n / d).divisors.filter (· ≤ V), Λ m : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U, ∑ m ∈ Finset.Icc 1 V,
            if d * m ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
                ((Λ m : ℂ) * χ (m : ZMod q) * χ ((n / (d * m) : ℕ) : ZMod q))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.mul_sum]
      have hsetD : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hsetD, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      by_cases hdn : d ∣ n
      · rw [if_pos hdn, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_sum,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter]
        have hsetM : (n / d).divisors.filter (· ≤ V) =
            (Finset.Icc 1 V).filter (fun m => d * m ∣ n) := by
          ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hm, _⟩, hmV⟩
            have hdm : d * m ∣ n := by
              obtain ⟨r, hr⟩ := hm
              exact ⟨r, by rw [← Nat.mul_div_cancel' hdn, hr]; ring⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hm (Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd1), hmV⟩, hdm⟩
          · rintro ⟨⟨_, hmV⟩, hdm⟩
            have hnd0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd1).ne'
            have hm : m ∣ n / d := by
              obtain ⟨r, hr⟩ := hdm
              refine ⟨r, Nat.eq_of_mul_eq_mul_left hd1 ?_⟩
              rw [Nat.mul_div_cancel' hdn, hr]; ring
            exact ⟨⟨hm, hnd0⟩, hmV⟩
        rw [hsetM]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hdm : d * m ∣ n := (Finset.mem_filter.mp hm).2
        have hmul : (n : ZMod q) = (d : ZMod q) * (m : ZMod q) * ((n / (d * m) : ℕ) : ZMod q) := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdm]
        rw [hmul, map_mul, map_mul]; ring
      · rw [if_neg hdn]
        symm
        refine Finset.sum_eq_zero fun m _ => if_neg fun hdm => hdn ((dvd_mul_right d m).trans hdm)
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hdm1 : 1 ≤ d * m := Nat.mul_pos hd1 hm1
    rw [← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / (d * m)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hr1 : 1 ≤ n / (d * m) := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hdm1
      exact ⟨hr1, (Nat.le_div_iff_mul_le hdm1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      refine ⟨d * m * r, ?_, Nat.mul_div_cancel_left r hdm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hdm1 hr.1, ?_⟩, dvd_mul_right (d * m) r⟩
      have := (Nat.le_div_iff_mul_le hdm1).mp hr.2
      rwa [mul_comm] at this
    · intro n _; ring
  -- Match S₃
  have hS3 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA3 U V n : ℂ) = vaughanS3 χ U V x := by
    unfold vaughanA3 vaughanS3
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ m ∈ n.divisors.filter (fun m => V < m ∧ U < n / m),
              Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc V (N / U),
            if m ∣ n ∧ U < n / m then
              (Λ m : ℂ) * χ (m : ZMod q) *
                ((vaughanMollifier U (n / m) : ℂ) * χ ((n / m : ℕ) : ZMod q))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_filter]
      have hset : n.divisors.filter (fun m => V < m ∧ U < n / m) =
          (Finset.Ioc V (N / U)).filter (fun m => m ∣ n ∧ U < n / m) := by
        ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hmn, _⟩, hVm, hUdiv⟩
          have hmU : m * U ≤ N := by
            have : m * U ≤ m * (n / m) := Nat.mul_le_mul_left m (by omega)
            rw [Nat.mul_div_cancel' hmn] at this
            exact this.trans hnN
          exact ⟨⟨hVm, (Nat.le_div_iff_mul_le hU).mpr hmU⟩, hmn, hUdiv⟩
        · rintro ⟨⟨hVm, _⟩, hmn, hUdiv⟩
          exact ⟨⟨hmn, by omega⟩, hVm, hUdiv⟩
      rw [hset]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmn : m ∣ n := (Finset.mem_filter.mp hm).2.1
      have hmul : (n : ZMod q) = (m : ZMod q) * ((n / m : ℕ) : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]
      rw [hmul, map_mul, Complex.ofReal_mul]; ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := by rw [Finset.mem_Ioc] at hm; omega
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.2.2, (Nat.le_div_iff_mul_le hm1).mpr (by rw [Nat.div_mul_cancel hn.2.1]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨m * k, ?_, Nat.mul_div_cancel_left k hm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hm1 (by omega), ?_⟩, dvd_mul_right m k, ?_⟩
      · have := (Nat.le_div_iff_mul_le hm1).mp hk.2
        rwa [mul_comm] at this
      · rw [Nat.mul_div_cancel_left k hm1]; exact hk.1
    · intro n _; rfl
  rw [hS0, hS1, hS2, hS3]

/-! ## Section 2: Unconditional Multiplicative Large Sieve & Pólya–Vinogradov Inequality -/

/-- Exact Gauss-sum modulus identity `|τ(χ)|² = q` for primitive Dirichlet characters `χ mod q`. -/
theorem gaussSum_norm_sq_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) :=
  Stage3BombieriVinogradov.norm_sq_gaussSum_eq hprim

open Classical in
/-- **Unconditional Multiplicative Large Sieve Inequality (`Finset.Ioc M (M + N)`)**:
`∑_{q=1}^Q (q / φ(q)) ∑*_{χ mod q} |∑_{n=M+1}^{M+N} a_n χ(n)|² ≤ (N + 3 Q²) ∑_{n=M+1}^{M+N} |a_n|²`. -/
theorem multiplicative_large_sieve_Ioc (Q M N : ℕ) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hIoc : Finset.Ioc M (M + N) = Finset.Ico (M + 1) ((M + 1) + N) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc]
  exact Stage3BombieriVinogradov.multiplicative_large_sieve_Ico Q (M + 1) N a

open Classical in
/-- **Unconditional Multiplicative Large Sieve Inequality on Arbitrary `Finset.Ioc M₁ M₂`**. -/
theorem multiplicative_large_sieve_Ioc_interval (Q M₁ M₂ : ℕ) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M₁ M₂, ‖a n‖ ^ 2 := by
  by_cases hle : M₁ ≤ M₂
  · have hEq : M₁ + (M₂ - M₁) = M₂ := Nat.add_sub_of_le hle
    simpa only [hEq] using multiplicative_large_sieve_Ioc Q M₁ (M₂ - M₁) a
  · have hempty : Finset.Ioc M₁ M₂ = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp

open Classical in
/-- **Unconditional Bilinear Multiplicative Large Sieve Inequality**:
for any `Q, M₁, M₂, N₁, N₂ : ℕ` and arbitrary complex sequences `a, b : ℕ → ℂ`,
`∑_{q ≤ Q} (q / φ(q)) ∑*_{χ mod q} |(∑_{m ∈ Ioc M₁ M₂} a_m χ(m)) (∑_{n ∈ Ioc N₁ N₂} b_n χ(n))| ≤ √((M₂-M₁)+3Q²) √((N₂-N₁)+3Q²) √(∑ |a_m|²) √(∑ |b_n|²)`. -/
theorem bilinear_multiplicative_large_sieve (Q M₁ M₂ N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖(∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))) *
              (∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1)))‖ ≤
      Real.sqrt (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) *
        Real.sqrt (((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2) := by
  let S : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range Q).sigma fun k =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => ((p.1 + 1 : ℕ) : ℝ) / (Nat.totient (p.1 + 1) : ℝ)
  let A : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => Real.sqrt (w p) * ‖∑ m ∈ Finset.Ioc M₁ M₂, a m * p.2 (m : ZMod (p.1 + 1))‖
  let B : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * p.2 (n : ZMod (p.1 + 1))‖
  have hw_nn : ∀ p : Σ k : ℕ, DirichletCharacter ℂ (k + 1), 0 ≤ w p := fun p => by
    dsimp only [w]; positivity
  have hLHS :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖(∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))) *
                (∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1)))‖ =
        ∑ p ∈ S, A p * B p := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    dsimp only [A, B, w]
    rw [norm_mul]
    have hsq : Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
        Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            (‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ *
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖)
        = (Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ))) *
            (‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ *
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖) := by rw [hsq]
      _ = _ := by ring
  have hCS : ∑ p ∈ S, A p * B p ≤
      Real.sqrt (∑ p ∈ S, A p ^ 2) * Real.sqrt (∑ p ∈ S, B p ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq S A B
    have hnn : 0 ≤ ∑ p ∈ S, A p * B p :=
      Finset.sum_nonneg fun p _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq
  have hA2 : ∑ p ∈ S, A p ^ 2 ≤
      (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2 := by
    have hEq : ∑ p ∈ S, A p ^ 2 =
        ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      dsimp only [A, w]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval Q M₁ M₂ a
  have hB2 : ∑ p ∈ S, B p ^ 2 ≤
      (((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2 := by
    have hEq : ∑ p ∈ S, B p ^ 2 =
        ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      dsimp only [B, w]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval Q N₁ N₂ b
  rw [hLHS]
  calc ∑ p ∈ S, A p * B p
      ≤ Real.sqrt (∑ p ∈ S, A p ^ 2) * Real.sqrt (∑ p ∈ S, B p ^ 2) := hCS
    _ ≤ Real.sqrt ((((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2) *
          Real.sqrt ((((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hB2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]; ring

/-- Lower bound on circle distance for reduced fractions: for `1 ≤ a < d`,
`distZ (a / d) ≥ min(a, d - a) / d > 0`. -/
private lemma distZ_div_ge_min {d a : ℕ} (ha1 : 1 ≤ a) (had : a < d) :
    ((min a (d - a) : ℕ) : ℝ) / (d : ℝ) ≤ Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold Stage3BombieriVinogradov.distZ Stage3BombieriVinogradov.fracSym
  set k : ℤ := round ((a : ℝ) / (d : ℝ))
  rcases le_or_gt k 0 with hk0 | hk1
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have ha_pos : (0 : ℝ) ≤ (a : ℝ) / (d : ℝ) := by positivity
    have hmin : ((min a (d - a) : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast Nat.min_le_left a (d - a)
    have h1 : (a : ℝ) / (d : ℝ) ≤ |(a : ℝ) / (d : ℝ) - (k : ℝ)| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    exact (div_le_div_of_nonneg_right hmin hd_pos.le).trans h1
  · have hk1' : (1 : ℤ) ≤ k := hk1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
    have hlt1 : (a : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_pos).mpr (by exact_mod_cast had)
    have hmin : ((min a (d - a) : ℕ) : ℝ) ≤ ((d - a : ℕ) : ℝ) := by
      exact_mod_cast Nat.min_le_right a (d - a)
    have hsub : ((d - a : ℕ) : ℝ) / (d : ℝ) = 1 - (a : ℝ) / (d : ℝ) := by
      rw [Nat.cast_sub had.le]; field_simp [hd_pos.ne']
    have h1 : 1 - (a : ℝ) / (d : ℝ) ≤ |(a : ℝ) / (d : ℝ) - (k : ℝ)| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    exact ((div_le_div_of_nonneg_right hmin hd_pos.le).trans_eq hsub).trans h1

/-- **Unconditional Pólya–Vinogradov Inequality (Primitive Characters)**:
for every `d ≥ 2` (`[NeZero d]`), every primitive `χ : DirichletCharacter ℂ d`, and every `N : ℕ`,
`‖∑_{n=1}^N χ(n)‖ ≤ √d * (1 + log d)`. -/
theorem polya_vinogradov_primitive {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ ≤ Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = d
    rw [DirichletCharacter.conductor_inv, hprim]
  have hgauss := Stage3BombieriVinogradov.gaussSum_mul_char_sum_eq hprim (Finset.Icc 1 N) (fun _ => (1 : ℂ))
  simp only [one_mul] at hgauss
  have hnorm_lhs : ‖gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ =
      Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ := by
    rw [norm_mul, Stage3BombieriVinogradov.norm_gaussSum_eq_sqrt hprim_inv]
  have hnorm_rhs :
      ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
          ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ ≤
        ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
    calc ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖
        ≤ ∑ a : (ZMod d)ˣ, ‖χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a : (ZMod d)ˣ,
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (χ⁻¹.norm_le_one _) (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ ∑ a ∈ Finset.Icc 1 (d - 1),
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖ := by
          let f : (ZMod d)ˣ → ℕ := fun u => (u : ZMod d).val
          have hinj : Set.InjOn f ((Finset.univ : Finset (ZMod d)ˣ) : Set (ZMod d)ˣ) := by
            intro u₁ _ u₂ _ h
            dsimp only [f] at h
            exact Units.ext (by rw [← ZMod.natCast_zmod_val (u₁ : ZMod d),
              ← ZMod.natCast_zmod_val (u₂ : ZMod d), h])
          have hsub : (Finset.univ : Finset (ZMod d)ˣ).image f ⊆ Finset.Icc 1 (d - 1) := by
            intro a ha
            obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
            rw [Finset.mem_Icc]
            have hlt : (u : ZMod d).val < d := ZMod.val_lt _
            have hne0 : (u : ZMod d).val ≠ 0 := by
              intro h0
              have hu0 : (u : ZMod d) = 0 := by rw [← ZMod.natCast_zmod_val (u : ZMod d), h0, Nat.cast_zero]
              have h10 : (1 : ZMod d) = 0 := by
                have := u.mul_inv; rw [hu0, zero_mul] at this; exact this.symm
              have : Fact (1 < d) := ⟨by omega⟩
              have hlt1 : (1 : ZMod d).val = 1 := ZMod.val_one d
              rw [h10, ZMod.val_zero] at hlt1; omega
            change 1 ≤ (u : ZMod d).val ∧ (u : ZMod d).val ≤ d - 1
            omega
          rw [← Finset.sum_image (f := fun a : ℕ =>
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖) hinj]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
      _ ≤ ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have had : a < d := by have := (Finset.mem_Icc.mp ha).2; omega
          have hmin_pos : (0 : ℝ) < ((min a (d - a) : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < min a (d - a) by omega)
          have hdist := distZ_div_ge_min ha1 had
          have hdist_pos : 0 < Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)) :=
            lt_of_lt_of_le (div_pos hmin_pos hd_pos) hdist
          have hIco :
              ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ))) =
                ∑ n ∈ Finset.Ico (1 : ℤ) ((1 : ℤ) + (N : ℤ)),
                  Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ))) := by
            refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
            · intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_Ico]; omega
            · intro n₁ _ n₂ _ h; exact Int.ofNat.inj h
            · intro z hz; simp only [Finset.mem_Ico] at hz
              exact ⟨z.toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro n _; simp
          rw [hIco]
          calc ‖∑ n ∈ Finset.Ico (1 : ℤ) ((1 : ℤ) + (N : ℤ)),
                  Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖
              ≤ (2 * Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)))⁻¹ :=
                Stage3BombieriVinogradov.norm_geom_sum_e_Ico_le 1 N hdist_pos
            _ ≤ (2 * (((min a (d - a) : ℕ) : ℝ) / (d : ℝ)))⁻¹ := by
                exact inv_anti₀ (by positivity) (by linarith)
            _ = (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
                field_simp [hd_pos.ne', hmin_pos.ne']
  -- Bound `∑_{a=1}^{d-1} d / (2 min(a, d-a)) ≤ d * (1 + log d)`
  have hsum_le :
      ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) ≤
        (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have hpair : ∀ a ∈ Finset.Icc 1 (d - 1),
        (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) ≤
          ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ) + (1 : ℝ) / ((d - a : ℕ) : ℝ)) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have had : a < d := by have := (Finset.mem_Icc.mp ha).2; omega
      have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
      have hda_pos : (0 : ℝ) < ((d - a : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      rcases le_total a (d - a) with h | h
      · rw [min_eq_left h]
        have hEq : (d : ℝ) / (2 * (a : ℝ)) = ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ)) := by ring
        rw [hEq]
        have hnn : 0 ≤ ((d : ℝ) / 2) * ((1 : ℝ) / ((d - a : ℕ) : ℝ)) := by positivity
        linarith
      · rw [min_eq_right h]
        have hEq : (d : ℝ) / (2 * ((d - a : ℕ) : ℝ)) =
            ((d : ℝ) / 2) * ((1 : ℝ) / ((d - a : ℕ) : ℝ)) := by ring
        rw [hEq]
        have hnn : 0 ≤ ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ)) := by positivity
        linarith
    have hrev :
        ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / ((d - a : ℕ) : ℝ) =
          ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) := by
      refine Finset.sum_bij (fun a _ => d - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Icc] at ha₁ ha₂; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb
        exact ⟨d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a _; rfl
    have hH : ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) ≤ 1 + Real.log (d : ℝ) := by
      calc ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ)
          ≤ ∑ a ∈ Finset.Icc 1 d, (1 : ℝ) / (a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
              fun _ _ _ => by positivity
        _ ≤ 1 + Real.log (d : ℝ) := Stage10ZeroDensity.sum_inv_le_one_add_log (by omega)
    calc ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ))
        ≤ ∑ a ∈ Finset.Icc 1 (d - 1),
            ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ) + (1 : ℝ) / ((d - a : ℕ) : ℝ)) :=
          Finset.sum_le_sum hpair
      _ = ((d : ℝ) / 2) *
            (∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) +
             ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / ((d - a : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = (d : ℝ) * ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) := by rw [hrev]; ring
      _ ≤ (d : ℝ) * (1 + Real.log (d : ℝ)) := mul_le_mul_of_nonneg_left hH hd_pos.le
  have hfinal : Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ ≤
      Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
    have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd_pos.le
    calc Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖
        = ‖gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ := hnorm_lhs.symm
      _ = ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ := by
          rw [hgauss]
      _ ≤ (d : ℝ) * (1 + Real.log (d : ℝ)) := hnorm_rhs.trans hsum_le
      _ = Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
          rw [← mul_assoc, hsq]
  exact le_of_mul_le_mul_left hfinal hsq_pos

/-- **Unconditional Log-Weighted Pólya–Vinogradov Inequality (Abel Summation)**:
for every `d ≥ 2` (`[NeZero d]`), every primitive `χ : DirichletCharacter ℂ d`, and every `N : ℕ`,
`‖∑_{n=1}^N χ(n) log n‖ ≤ 2 * √d * (1 + log d) * Real.log (max 1 N)`. -/
theorem polya_vinogradov_log_primitive {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * (Real.log (n : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log ((max 1 N : ℕ) : ℝ) := by
  set M : ℝ := Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))
  have hM_nn : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; linarith)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hmax : max 1 N = N := Nat.max_eq_right hN
    rw [hmax]
    let S : ℕ → ℂ := fun m => ∑ j ∈ Finset.Icc 1 m, χ (j : ZMod d)
    have hS0 : S 0 = 0 := by simp [S]
    have hS_step : ∀ m : ℕ, 1 ≤ m → χ (m : ZMod d) = S m - S (m - 1) := by
      intro m hm
      dsimp only [S]
      have hIcc : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp; omega)]
      ring
    -- Abel summation identity
    have habel : ∀ K : ℕ, 1 ≤ K →
        ∑ n ∈ Finset.Icc 1 K, χ (n : ZMod d) * (Real.log (n : ℝ) : ℂ) =
          S K * (Real.log (K : ℝ) : ℂ) -
            ∑ m ∈ Finset.Icc 1 (K - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ)) := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have hIcc1 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hIcc2 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc1, Finset.sum_insert (by simp), ih, Nat.add_sub_cancel, hIcc2,
          Finset.sum_insert (by simp; omega), hS_step (k + 1) (by omega), Nat.add_sub_cancel]
        push_cast
        ring
    rw [habel N hN]
    have hS_bd : ∀ m : ℕ, ‖S m‖ ≤ M := fun m => polya_vinogradov_primitive hd2 hprim m
    have htele :
        ∑ m ∈ Finset.Icc 1 (N - 1), (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) =
          Real.log (N : ℝ) := by
      have h1 : ∀ K : ℕ, 1 ≤ K →
          ∑ m ∈ Finset.Icc 1 (K - 1), (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) =
            Real.log (K : ℝ) := by
        intro K hK
        induction K, hK using Nat.le_induction with
        | base => simp
        | succ k hk ih =>
          have hIcc2 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [Nat.add_sub_cancel, hIcc2, Finset.sum_insert (by simp; omega), ih]
          ring
      exact h1 N hN
    calc ‖S N * (Real.log (N : ℝ) : ℂ) -
            ∑ m ∈ Finset.Icc 1 (N - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ))‖
        ≤ ‖S N * (Real.log (N : ℝ) : ℂ)‖ +
            ‖∑ m ∈ Finset.Icc 1 (N - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ ‖S N‖ * Real.log (N : ℝ) +
            ∑ m ∈ Finset.Icc 1 (N - 1),
              ‖S m‖ * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
          have hterm1 : ‖S N * (Real.log (N : ℝ) : ℂ)‖ = ‖S N‖ * Real.log (N : ℝ) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg N)]
          rw [hterm1]
          gcongr
          refine (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hdiff_nn : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
            have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
            have := Real.log_le_log (Nat.cast_pos.mpr hm1) hm_le
            linarith
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdiff_nn]
      _ ≤ M * Real.log (N : ℝ) +
            ∑ m ∈ Finset.Icc 1 (N - 1), M * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right (hS_bd N) (Real.log_natCast_nonneg N)) ?_
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
          have hdiff_nn : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
            linarith [Real.log_le_log (Nat.cast_pos.mpr hm1) hm_le]
          exact mul_le_mul_of_nonneg_right (hS_bd m) hdiff_nn
      _ = M * Real.log (N : ℝ) + M * Real.log (N : ℝ) := by
          rw [← Finset.mul_sum, htele]
      _ = 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log (N : ℝ) := by
          dsimp only [M]; ring

/-! ## Section 3: Unconditional Type 0, Type I & Type II Dyadic Primitive-Character Bounds -/

open Classical in
/-- Sum of primitive character weights `∑_{q ≤ Q} (q / φ(q)) * #{χ mod q : χ.IsPrimitive} ≤ Q²`. -/
private lemma sum_prim_weight_le (Q : ℕ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
      (Q : ℝ) ^ 2 := by
  calc ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
      ≤ ∑ k ∈ Finset.range Q, (Q : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkQ : k + 1 ≤ Q := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
          Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
        have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
        have hcard :
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
              (Nat.totient (k + 1) : ℝ) := by
          have hnat : (Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card ≤
              (k + 1).totient := by
            calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).card := Finset.card_filter_le _ _
              _ = (k + 1).totient := by rw [Finset.card_univ, htot]
          exact_mod_cast hnat
        calc (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
            ≤ (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) * (Nat.totient (k + 1) : ℝ) :=
              mul_le_mul_of_nonneg_left hcard (by positivity)
          _ = ((k + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hphi_pos.ne'
          _ ≤ (Q : ℝ) := by exact_mod_cast hkQ
    _ = (Q : ℝ) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq]

/-- Pointwise bound on Vaughan Type 0 sum: `‖S₀(χ; V, x)‖ ≤ V * log x`. -/
theorem norm_vaughanS0_le {q : ℕ} (χ : DirichletCharacter ℂ q) (V : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖vaughanS0 χ V x‖ ≤ (V : ℝ) * Real.log x := by
  unfold vaughanS0
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ‖∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), χ (n : ZMod q) * (Λ n : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), ‖χ (n : ZMod q) * (Λ n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), Real.log x := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnx : (n : ℝ) ≤ x :=
          (by exact_mod_cast ((Finset.mem_Icc.mp hn).2.trans (Nat.min_le_left _ _)) : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
            (Nat.floor_le (by linarith))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc ‖χ (n : ZMod q)‖ * Λ n
            ≤ 1 * Λ n := mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
          _ = Λ n := one_mul _
          _ ≤ Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr hn1) hnx
    _ = ((Finset.Icc 1 (min ⌊x⌋₊ V)).card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (V : ℝ) * Real.log x := by
        refine mul_le_mul_of_nonneg_right ?_ hlogx_nn
        have hcard : (Finset.Icc 1 (min ⌊x⌋₊ V)).card ≤ V := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast hcard

/-- Pointwise Pólya–Vinogradov bound on Vaughan Type I sum `S₁(χ; U, x)`. -/
theorem norm_vaughanS1_le {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (U : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖vaughanS1 χ U x‖ ≤ 2 * (U : ℝ) * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
  unfold vaughanS1
  have hM_nn : 0 ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; positivity
  calc ‖∑ k ∈ Finset.Icc 1 U,
          (ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖
      ≤ ∑ k ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 U,
          2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul]
        have hmu : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
          by_cases hsq : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp [norm_pow]
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
        have hfac : ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ ≤ 1 :=
          (mul_le_mul hmu (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
        have hmax_le : ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) ≤ x := by
          rcases le_total 1 (⌊x⌋₊ / k) with h | h
          · rw [Nat.max_eq_right h]
            exact (by exact_mod_cast Nat.div_le_self ⌊x⌋₊ k : ((⌊x⌋₊ / k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
              (Nat.floor_le (by linarith))
          · rw [Nat.max_eq_left h]; exact_mod_cast hx
        have hlog_le : Real.log ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) ≤ Real.log x :=
          Real.log_le_log (by exact_mod_cast (show 0 < max 1 (⌊x⌋₊ / k) by omega)) hmax_le
        calc ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ *
                ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖
            ≤ 1 * ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
          _ = ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ := one_mul _
          _ ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) *
                Real.log ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) :=
              polya_vinogradov_log_primitive hd2 hprim (⌊x⌋₊ / k)
          _ ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x :=
              mul_le_mul_of_nonneg_left hlog_le hM_nn
    _ = ((Finset.Icc 1 U).card : ℝ) * (2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (U : ℝ) * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]; ring

/-- Pointwise Pólya–Vinogradov bound on Vaughan Type I sum `S₂(χ; U, V, x)`. -/
theorem norm_vaughanS2_le {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {U V : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hVx : (V : ℝ) ≤ x) :
    ‖vaughanS2 χ U V x‖ ≤ (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
  unfold vaughanS2
  have hM_nn : 0 ≤ Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; positivity
  calc ‖∑ k ∈ Finset.Icc 1 U,
          (ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
              ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖
      ≤ ∑ k ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
              ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 U,
          (V : ℝ) * Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul]
        have hmu : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
          by_cases hsq : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp [norm_pow]
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
        have hfac : ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ ≤ 1 :=
          (mul_le_mul hmu (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
        refine (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans ?_
        rw [one_mul]
        calc ‖∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
                ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖
            ≤ ∑ m ∈ Finset.Icc 1 V, ‖(Λ m : ℂ) * χ (m : ZMod d) *
                ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ Finset.Icc 1 V, Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
              have hmx : (m : ℝ) ≤ x :=
                (by exact_mod_cast (Finset.mem_Icc.mp hm).2 : (m : ℝ) ≤ (V : ℝ)).trans hVx
              rw [norm_mul, norm_mul, Complex.norm_real,
                Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
              have hL : Λ m * ‖χ (m : ZMod d)‖ ≤ Real.log x := by
                calc Λ m * ‖χ (m : ZMod d)‖
                    ≤ Λ m * 1 := mul_le_mul_of_nonneg_left (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
                  _ = Λ m := mul_one _
                  _ ≤ Real.log (m : ℝ) := ArithmeticFunction.vonMangoldt_le_log
                  _ ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr hm1) hmx
              exact mul_le_mul hL (polya_vinogradov_primitive hd2 hprim (⌊x⌋₊ / (k * m)))
                (norm_nonneg _) (Real.log_nonneg hx)
          _ = (V : ℝ) * Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
              rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ = (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

/-! ### Sub-dyadic Rectangle + Thin-Annulus Boundary Decomposition of `vaughanS3` -/

/-- Lower endpoint `V * 2^r` of the `r`-th dyadic block in `vaughanS3`. -/
private def blockLo (V r : ℕ) : ℕ := V * 2 ^ r

/-- Upper endpoint `min (V * 2^(r+1)) (N / U)` of the `r`-th dyadic block. -/
private def blockHi (N U V r : ℕ) : ℕ := min (V * 2 ^ (r + 1)) (N / U)

/-- Sub-interval step `max 1 ⌊Δ * (V * 2^r)⌋₊` inside the `r`-th dyadic block. -/
private def blockStep (V : ℕ) (Δ : ℝ) (r : ℕ) : ℕ :=
  max 1 ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊

/-- Number of sub-intervals partitioning the `r`-th dyadic block. -/
private def blockCount (N U V : ℕ) (Δ : ℝ) (r : ℕ) : ℕ :=
  (blockHi N U V r - blockLo V r + blockStep V Δ r - 1) / blockStep V Δ r

/-- Lower endpoint of the `(r, j)` sub-interval. -/
private def subLo (V : ℕ) (Δ : ℝ) (r j : ℕ) : ℕ :=
  blockLo V r + j * blockStep V Δ r

/-- Upper endpoint of the `(r, j)` sub-interval. -/
private def subHi (N U V : ℕ) (Δ : ℝ) (r j : ℕ) : ℕ :=
  min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi N U V r)

/-- Exact splitting of a sum over `Finset.Ioc a b` at any intermediate cutoff `c ≥ a`. -/
private lemma sum_Ioc_split {α : Type*} [AddCommMonoid α] (a b c : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc a b, f m = ∑ m ∈ Finset.Ioc a c, f m + ∑ m ∈ Finset.Ioc c b, f m := by
  have hunion : Finset.Ioc a b = Finset.Ioc a c ∪ Finset.Ioc c b := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ioc a c) (Finset.Ioc c b) := by
    rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Ioc] at h1 h2; omega
  rw [hunion, Finset.sum_union hdisj]

/-- Exact dyadic partition of a sum over `Finset.Ioc V (N / U)` into `R = Nat.log 2 N + 1` blocks. -/
private lemma sum_Ioc_dyadic {α : Type*} [AddCommMonoid α] (N U V : ℕ) (_hU : 1 ≤ U) (hV : 1 ≤ V)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc V (N / U), f m =
      ∑ r ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ Finset.Ioc (blockLo V r) (blockHi N U V r), f m := by
  have hstep : ∀ R : ℕ,
      ∑ m ∈ Finset.Ioc V (min (V * 2 ^ R) (N / U)), f m =
        ∑ r ∈ Finset.range R, ∑ m ∈ Finset.Ioc (blockLo V r) (blockHi N U V r), f m := by
    intro R
    induction R with
    | zero =>
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty]
      have : Finset.Ioc V (min V (N / U)) = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
    | succ R ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases hle : V * 2 ^ R ≤ N / U
      · have hmin1 : min (V * 2 ^ R) (N / U) = V * 2 ^ R := Nat.min_eq_left hle
        rw [hmin1]
        have hVle : V ≤ V * 2 ^ R := Nat.le_mul_of_pos_right V (by positivity)
        have hRle : V * 2 ^ R ≤ min (V * 2 ^ (R + 1)) (N / U) :=
          le_min (Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ R))) hle
        exact sum_Ioc_split V (min (V * 2 ^ (R + 1)) (N / U)) (V * 2 ^ R) hVle hRle f
      · have hmin1 : min (V * 2 ^ R) (N / U) = N / U := Nat.min_eq_right (by omega)
        have hmin2 : min (V * 2 ^ (R + 1)) (N / U) = N / U := by
          apply Nat.min_eq_right
          have : V * 2 ^ R ≤ V * 2 ^ (R + 1) :=
            Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ R))
          omega
        have hempty : Finset.Ioc (blockLo V R) (blockHi N U V R) = ∅ := by
          unfold blockLo blockHi; rw [hmin2]; exact Finset.Ioc_eq_empty (by omega)
        rw [hmin1, hmin2, hempty, Finset.sum_empty, add_zero]
  have htop : N / U ≤ V * 2 ^ (Nat.log 2 N + 1) := by
    have h1 : N / U ≤ N := Nat.div_le_self N U
    have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
    have h3 : 2 ^ (Nat.log 2 N + 1) ≤ V * 2 ^ (Nat.log 2 N + 1) := Nat.le_mul_of_pos_left _ hV
    omega
  have hmin : min (V * 2 ^ (Nat.log 2 N + 1)) (N / U) = N / U := Nat.min_eq_right htop
  rw [← hmin]
  exact hstep (Nat.log 2 N + 1)

/-- Exact uniform sub-interval partition of `Finset.Ioc a b` with step `h ≥ 1`. -/
private lemma sum_Ioc_uniform {α : Type*} [AddCommMonoid α] (a b h L : ℕ) (hL : b ≤ a + L * h)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc a b, f m =
      ∑ j ∈ Finset.range L, ∑ m ∈ Finset.Ioc (a + j * h) (min (a + (j + 1) * h) b), f m := by
  have hgen : ∀ K : ℕ,
      ∑ m ∈ Finset.Ioc a (min (a + K * h) b), f m =
        ∑ j ∈ Finset.range K, ∑ m ∈ Finset.Ioc (a + j * h) (min (a + (j + 1) * h) b), f m := by
    intro K
    induction K with
    | zero =>
      simp only [zero_mul, add_zero, Finset.range_zero, Finset.sum_empty]
      have : Finset.Ioc a (min a b) = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
    | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases hle : a + K * h ≤ b
      · have hmin1 : min (a + K * h) b = a + K * h := Nat.min_eq_left hle
        rw [hmin1]
        have hstep_le : a + K * h ≤ min (a + (K + 1) * h) b :=
          le_min (by nlinarith) hle
        exact sum_Ioc_split a (min (a + (K + 1) * h) b) (a + K * h) (by omega) hstep_le f
      · have hmin1 : min (a + K * h) b = b := Nat.min_eq_right (by omega)
        have hmin2 : min (a + (K + 1) * h) b = b := Nat.min_eq_right (by nlinarith)
        have hempty : Finset.Ioc (a + K * h) (min (a + (K + 1) * h) b) = ∅ := by
          rw [hmin2]; exact Finset.Ioc_eq_empty (by omega)
        rw [hempty, hmin1, hmin2, Finset.sum_empty, add_zero]
  have hmin : min (a + L * h) b = b := Nat.min_eq_right hL
  conv_lhs => rw [← hmin]
  exact hgen L

/-- Covering property `blockHi ≤ blockLo + blockCount * blockStep`. -/
private lemma blockHi_le_blockLo_add_count_mul_step (N U V : ℕ) (Δ : ℝ) (r : ℕ) :
    blockHi N U V r ≤ blockLo V r + blockCount N U V Δ r * blockStep V Δ r := by
  unfold blockCount
  set a := blockLo V r
  set b := blockHi N U V r
  set h := blockStep V Δ r
  have hh : 1 ≤ h := le_max_left 1 _
  by_cases hba : b ≤ a
  · omega
  · have hdiv := Nat.div_add_mod (b - a + h - 1) h
    have hmod : (b - a + h - 1) % h < h := Nat.mod_lt _ (by omega)
    have hmul : b - a ≤ (b - a + h - 1) / h * h := by
      have : h * ((b - a + h - 1) / h) + (b - a + h - 1) % h = b - a + h - 1 := hdiv
      have hcomm : h * ((b - a + h - 1) / h) = (b - a + h - 1) / h * h := mul_comm _ _
      omega
    omega

/-- Decoupled rectangular main part of `vaughanS3` at mesh `Δ ∈ (0, 1)`. -/
private def vaughanS3Rect {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x Δ : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), (Λ m : ℂ) * χ (m : ZMod q)) *
      (∑ k ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), (vaughanMollifier U k : ℂ) * χ (k : ZMod q))

/-- Thin-annulus boundary part of `vaughanS3` at mesh `Δ ∈ (0, 1)`. -/
private def vaughanS3Bdy {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x Δ : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
        (Λ m : ℂ) * χ (m : ZMod q) *
          ∑ k ∈ Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m),
            (vaughanMollifier U k : ℂ) * χ (k : ZMod q)

/-- Exact identity `vaughanS3 = vaughanS3Rect + vaughanS3Bdy`. -/
private lemma vaughanS3_eq_rect_add_bdy {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x Δ : ℝ) :
    vaughanS3 χ U V x = vaughanS3Rect χ U V x Δ + vaughanS3Bdy χ U V x Δ := by
  unfold vaughanS3 vaughanS3Rect vaughanS3Bdy
  rw [sum_Ioc_dyadic ⌊x⌋₊ U V hU hV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_Ioc_uniform (blockLo V r) (blockHi ⌊x⌋₊ U V r) (blockStep V Δ r) (blockCount ⌊x⌋₊ U V Δ r)
    (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmb : m ≤ subHi ⌊x⌋₊ U V Δ r j := (Finset.mem_Ioc.mp hm).2
  have hm_pos : 0 < m := by
    have h1 := (Finset.mem_Ioc.mp hm).1
    have hlo : 1 ≤ blockLo V r := Nat.mul_pos hV (by positivity)
    unfold subLo at h1; omega
  have hdiv_le : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j ≤ ⌊x⌋₊ / m :=
    Nat.div_le_div_left hmb hm_pos
  rw [← mul_add]
  congr 1
  by_cases hUle : U ≤ ⌊x⌋₊ / m
  · have h1 : U ≤ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) := le_max_left _ _
    have h2 : max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) ≤ ⌊x⌋₊ / m := max_le hUle hdiv_le
    have hsplit := sum_Ioc_split U (⌊x⌋₊ / m) (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) h1 h2
      (fun k => (vaughanMollifier U k : ℂ) * χ (k : ZMod q))
    rw [hsplit]
    congr 1
    have hIoc_eq : Finset.Ioc U (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) =
        Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) := by
      ext k; simp only [Finset.mem_Ioc]; omega
    rw [hIoc_eq]
  · have he1 : Finset.Ioc U (⌊x⌋₊ / m) = ∅ := Finset.Ioc_eq_empty (by omega)
    have he2 : Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) = ∅ := Finset.Ioc_eq_empty (by omega)
    have he3 : Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m) = ∅ :=
      Finset.Ioc_eq_empty (by omega)
    rw [he1, he2, he3]; simp

/-- Character-independent boundary coefficient `bdyCoeff U V x Δ n` supported on the thin annulus
`(⌊x / (1 + Δ)⌋₊, ⌊x⌋₊]`. -/
private def bdyCoeff (U V : ℕ) (x Δ : ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
          (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
        Λ m * vaughanMollifier U (n / m)

/-- Key thin-annulus containment: every boundary pair `(m, k)` satisfies
`m * k ∈ Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊`. -/
private lemma bdy_prod_mem_annulus {U V r j m k : ℕ} {x Δ : ℝ}
    (_hV : 1 ≤ V) (hx : 1 ≤ x) (hΔ0 : 0 < Δ)
    (hm : m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j))
    (hk : k ∈ Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m)) :
    m * k ∈ Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊ := by
  simp only [Finset.mem_Ioc] at hm hk ⊢
  set a := subLo V Δ r j
  set b := subHi ⌊x⌋₊ U V Δ r j
  set h := blockStep V Δ r
  have hmk_le : m * k ≤ ⌊x⌋₊ := by
    calc m * k ≤ m * (⌊x⌋₊ / m) := Nat.mul_le_mul_left m hk.2
      _ ≤ ⌊x⌋₊ := Nat.mul_div_le ⌊x⌋₊ m
  have hm_lt_b : m < b := by
    by_contra hge
    have hmb : m = b := by omega
    rw [hmb] at hk
    have : ⌊x⌋₊ / b < k := lt_of_le_of_lt (le_max_right _ _) hk.1
    omega
  have hb_le_ah : b ≤ a + h := by
    dsimp only [a, b, subLo, subHi]
    calc min (blockLo V r + (j + 1) * h) (blockHi ⌊x⌋₊ U V r)
        ≤ blockLo V r + (j + 1) * h := Nat.min_le_left _ _
      _ = blockLo V r + j * h + h := by ring
  have hh_ge2 : 2 ≤ h := by
    have ha_lt_m : a < m := hm.1
    omega
  have hh_eq : h = ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊ := by
    rcases le_total 1 ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊ with h1 | h1
    · exact max_eq_right h1
    · have hh1 : h = 1 := max_eq_left h1
      omega
  have hh_le_R : (h : ℝ) ≤ Δ * (a : ℝ) := by
    have h1 : (h : ℝ) ≤ Δ * ((blockLo V r : ℕ) : ℝ) := by
      rw [hh_eq]; exact Nat.floor_le (by positivity)
    have h2 : ((blockLo V r : ℕ) : ℝ) ≤ (a : ℝ) := by
      dsimp only [a, subLo]; exact_mod_cast Nat.le_add_right (blockLo V r) (j * h)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hΔ0.le)
  have hb_le_R : (b : ℝ) ≤ (1 + Δ) * (a : ℝ) := by
    have hbaR : (b : ℝ) ≤ (a : ℝ) + (h : ℝ) := by exact_mod_cast hb_le_ah
    linarith
  have hbk_gt_x : x < (b : ℝ) * (k : ℝ) := by
    have hk_gt : ⌊x⌋₊ / b < k := lt_of_le_of_lt (le_max_right _ _) hk.1
    have hbk_nat : ⌊x⌋₊ + 1 ≤ b * k := by
      have hdiv := Nat.div_add_mod ⌊x⌋₊ b
      have hb_pos : 0 < b := by omega
      have hmod : ⌊x⌋₊ % b < b := Nat.mod_lt _ hb_pos
      have h1 : ⌊x⌋₊ < b * (⌊x⌋₊ / b + 1) := by nlinarith
      have h2 : b * (⌊x⌋₊ / b + 1) ≤ b * k := Nat.mul_le_mul_left b hk_gt
      omega
    have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hbkR : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((b * k : ℕ) : ℝ) := by exact_mod_cast hbk_nat
    push_cast at hbkR
    linarith
  have hmk_gt : x / (1 + Δ) < ((m * k : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 + Δ)]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have ham : (a : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have h1 : (b : ℝ) * (k : ℝ) ≤ (1 + Δ) * (a : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hb_le_R hk_pos.le
    have h2 : (1 + Δ) * (a : ℝ) * (k : ℝ) < (1 + Δ) * (m : ℝ) * (k : ℝ) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left ham (by linarith)) hk_pos
    have h3 : (1 + Δ) * (m : ℝ) * (k : ℝ) = ((m * k : ℕ) : ℝ) * (1 + Δ) := by push_cast; ring
    linarith
  have hfl_le : (⌊x / (1 + Δ)⌋₊ : ℝ) ≤ x / (1 + Δ) := Nat.floor_le (by positivity)
  have hlt_nat : ⌊x / (1 + Δ)⌋₊ < m * k := by
    exact_mod_cast lt_of_le_of_lt hfl_le hmk_gt
  exact ⟨hlt_nat, hmk_le⟩

/-- Exact character-sum representation of `vaughanS3Bdy` on the thin annulus `(⌊x/(1+Δ)⌋₊, ⌊x⌋₊]`. -/
private lemma vaughanS3Bdy_eq_annulus_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hV : 1 ≤ V) {x Δ : ℝ} (hx : 1 ≤ x) (hΔ0 : 0 < Δ) :
    vaughanS3Bdy χ U V x Δ =
      ∑ n ∈ Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊, (bdyCoeff U V x Δ n : ℂ) * χ (n : ZMod q) := by
  set I := Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
  unfold vaughanS3Bdy bdyCoeff
  -- Expand RHS sum over `n ∈ I`, swap `(n, r, j)` to `(r, j, n)`
  have hRHS :
      ∑ n ∈ I,
          ((∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
            ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
              ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                  (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
                Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) * χ (n : ZMod q) =
        ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ n ∈ I,
              ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                  (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
                ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
    have h1 : ∀ n ∈ I,
        ((∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
              Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) * χ (n : ZMod q) =
        ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
              ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
      intro n _
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
  rw [hRHS]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  -- Swap `(n, m)` to `(m, k)` with `n = m * k`
  set S_m := Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)
  set K_lo := max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)
  have hswap :
      ∑ n ∈ I, ∑ m ∈ S_m.filter (fun m => m ∣ n ∧ K_lo < n / m),
          ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) =
        ∑ m ∈ S_m, ∑ n ∈ I.filter (fun n => m ∣ n ∧ K_lo < n / m),
          ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
    have hL : ∀ n ∈ I,
        ∑ m ∈ S_m.filter (fun m => m ∣ n ∧ K_lo < n / m),
            ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) =
          ∑ m ∈ S_m, if m ∣ n ∧ K_lo < n / m then
            ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) else 0 :=
      fun _ _ => Finset.sum_filter _ _
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => (Finset.sum_filter _ _).symm
  rw [hswap]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_pos : 0 < m := by
    have h1 := (Finset.mem_Ioc.mp hm).1
    have hlo : 1 ≤ blockLo V r := Nat.mul_pos hV (by positivity)
    unfold subLo at h1; omega
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, I] at hn ⊢
    exact ⟨hn.2.2, (Nat.le_div_iff_mul_le hm_pos).mpr (by rw [Nat.div_mul_cancel hn.2.1]; exact hn.1.2)⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
        ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
  · intro k hk
    refine ⟨m * k, ?_, Nat.mul_div_cancel_left k hm_pos⟩
    have hmemI : m * k ∈ I := bdy_prod_mem_annulus hV hx hΔ0 hm hk
    refine Finset.mem_filter.mpr ⟨hmemI, dvd_mul_right m k, ?_⟩
    rw [Nat.mul_div_cancel_left k hm_pos]
    exact (Finset.mem_Ioc.mp hk).1
  · intro n hn
    have hmn : m ∣ n := (Finset.mem_filter.mp hn).2.1
    have hmul : (n : ZMod q) = (m : ZMod q) * ((n / m : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]
    rw [hmul, map_mul]; ring

/-- Pointwise divisor bound on the boundary coefficient: `|bdyCoeff U V x Δ n| ≤ d(n) * log x`
for every `1 ≤ n ≤ ⌊x⌋₊`. -/
private lemma abs_bdyCoeff_le {U V n : ℕ} {x Δ : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hn1 : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    |bdyCoeff U V x Δ n| ≤ (n.divisors.card : ℝ) * Real.log x := by
  unfold bdyCoeff
  have hinner :
      |∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
              (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
            Λ m * vaughanMollifier U (n / m)| ≤
      ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
            if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun m _ => ?_
    split_ifs with h1 h2
    · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      refine (abs_vaughanMollifier_le_divisors U (n / m)).trans ?_
      have hdvd : n / m ∣ n := Nat.div_dvd_of_dvd h1.1
      have hsub : (n / m).divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd (by omega) hdvd
      exact_mod_cast Finset.card_le_card hsub
    · exact absurd h1.1 h2
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    · exact le_rfl
  -- Collapse the `(r, j)` partition back into `Finset.Ioc V (⌊x⌋₊ / U)`!
  have hcollapse :
      ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
            (if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0) =
        ∑ m ∈ Finset.Ioc V (⌊x⌋₊ / U),
          if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0 := by
    rw [sum_Ioc_dyadic ⌊x⌋₊ U V hU hV]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact (sum_Ioc_uniform (blockLo V r) (blockHi ⌊x⌋₊ U V r) (blockStep V Δ r) (blockCount ⌊x⌋₊ U V Δ r)
      (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r) _).symm
  refine hinner.trans ?_
  rw [hcollapse, ← Finset.sum_filter]
  have hsub : (Finset.Ioc V (⌊x⌋₊ / U)).filter (fun m => m ∣ n) ⊆ n.divisors := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, by omega⟩
  calc ∑ m ∈ (Finset.Ioc V (⌊x⌋₊ / U)).filter (fun m => m ∣ n), Λ m * (n.divisors.card : ℝ)
      ≤ ∑ m ∈ n.divisors, Λ m * (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ = (∑ m ∈ n.divisors, Λ m) * (n.divisors.card : ℝ) := (Finset.sum_mul _ _ _).symm
    _ = Real.log (n : ℝ) * (n.divisors.card : ℝ) := by rw [ArithmeticFunction.vonMangoldt_sum]
    _ ≤ Real.log x * (n.divisors.card : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact Real.log_le_log (Nat.cast_pos.mpr hn1)
          ((by exact_mod_cast hnx : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith)))
    _ = (n.divisors.card : ℝ) * Real.log x := mul_comm _ _

/-- Elementary `sqrt (a + b) ≤ sqrt a + sqrt b`. -/
private lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsq : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by positivity
    linarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

open Classical in
/-- **Unconditional Large-Sieve Bound on the Thin-Annulus Boundary Sum `vaughanS3Bdy`**:
for `1 ≤ D`, `1 ≤ U`, `1 ≤ V`, `3 ≤ x`, `0 < Δ < 1`,
`∑_{q ≤ 2D} (q / φ(q)) ∑*_{χ mod q} ‖vaughanS3Bdy χ U V x Δ‖ ≤ 2 D (√Δ x + √x + 4 D √x) (1 + log x)³`. -/
private lemma sum_vaughanS3Bdy_le {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ ≤
      2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) *
        (1 + Real.log x) ^ 3 := by
  have hx1 : 1 ≤ x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx1)
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  set I := Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
  -- Cauchy–Schwarz over `(k, χ)`
  let S : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range (2 * D)).sigma fun k =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => ((p.1 + 1 : ℕ) : ℝ) / (Nat.totient (p.1 + 1) : ℝ)
  have hLHS :
      ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖vaughanS3Bdy χ U V x Δ‖ =
        ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    dsimp only [w]
    rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]
  have hCS :
      ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) ≤
        Real.sqrt (∑ p ∈ S, w p) *
          Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun p => Real.sqrt (w p)) (fun p => Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖)
    have hW : ∑ p ∈ S, (Real.sqrt (w p)) ^ 2 = ∑ p ∈ S, w p :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (by dsimp only [w]; positivity)
    have hV2 : ∑ p ∈ S, (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) ^ 2 =
        ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow, Real.sq_sqrt (by dsimp only [w]; positivity)]
    rw [hW, hV2] at h1
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun p _ => by dsimp only [w]; positivity)]
    exact Real.le_sqrt_of_sq_le h1
  have hW_le : ∑ p ∈ S, w p ≤ (2 * (D : ℝ)) ^ 2 := by
    have hEq : ∑ p ∈ S, w p =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hEq]
    simpa [Nat.cast_mul] using sum_prim_weight_le (2 * D)
  have hLS :
      ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 ≤
        (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
          ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 := by
    have hEq : ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ I, (bdyCoeff U V x Δ n : ℂ) * χ (n : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [vaughanS3Bdy_eq_annulus_sum χ hV hx1 hΔ0]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval (2 * D) ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
      (fun n => (bdyCoeff U V x Δ n : ℂ))
  -- Bound annulus length `⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ ≤ Δ * x + 1`
  have hlen : ((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) ≤ Δ * x + 1 := by
    have hle_fl : ⌊x / (1 + Δ)⌋₊ ≤ ⌊x⌋₊ :=
      Nat.floor_mono (div_le_self (by linarith) (by linarith))
    rw [Nat.cast_sub hle_fl]
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h2 : x / (1 + Δ) - 1 < (⌊x / (1 + Δ)⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (x / (1 + Δ))]
    have h3 : x - x / (1 + Δ) ≤ Δ * x := by
      have hEq : x - x / (1 + Δ) = (Δ / (1 + Δ)) * x := by field_simp [(by linarith : 1 + Δ ≠ 0)]; ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right (div_le_self hΔ0.le (by linarith)) (by linarith)
    linarith
  -- Bound `∑ n ∈ I, ‖bdyCoeff n‖² ≤ x * (1 + log x)^5`
  have hL2 : ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 ≤ x * (1 + Real.log x) ^ 5 := by
    have hI_sub : I ⊆ Finset.Icc 1 ⌊x⌋₊ := by
      intro n hn; simp only [I, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
    calc ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hI_sub fun _ _ _ => sq_nonneg _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.divisors.card : ℝ) * Real.log x) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_bdyCoeff_le hU hV hx1 (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2) 2
      _ = (Real.log x) ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
      _ ≤ (Real.log x) ^ 2 * ((⌊x⌋₊ : ℝ) * (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 3) :=
          mul_le_mul_of_nonneg_left (Stage10ZeroDensity.sum_divisors_card_sq_le hN1) (sq_nonneg _)
      _ ≤ (1 + Real.log x) ^ 2 * (x * (1 + Real.log x) ^ 3) := by
          have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
          have hlog_fl : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
            Real.log_le_log (Nat.cast_pos.mpr hN1) hfl_le
          gcongr
          linarith
      _ = x * (1 + Real.log x) ^ 5 := by ring
  -- Combine all factors
  have hsqrtW : Real.sqrt (∑ p ∈ S, w p) ≤ 2 * (D : ℝ) :=
    (Real.sqrt_le_sqrt hW_le).trans_eq (Real.sqrt_sq (by positivity))
  have hfac1 : Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2)) ≤
      Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ) := by
    have hbound : (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) ≤
        Δ * x + 1 + 16 * (D : ℝ) ^ 2 := by
      have hcast : 3 * ((2 * D : ℕ) : ℝ) ^ 2 = 12 * (D : ℝ) ^ 2 := by push_cast; ring
      nlinarith
    calc Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2))
        ≤ Real.sqrt (Δ * x + 1 + 16 * (D : ℝ) ^ 2) := Real.sqrt_le_sqrt hbound
      _ ≤ Real.sqrt (Δ * x + 1) + Real.sqrt (16 * (D : ℝ) ^ 2) :=
          sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
      _ ≤ (Real.sqrt (Δ * x) + Real.sqrt 1) + Real.sqrt ((4 * (D : ℝ)) ^ 2) := by
          have h1 := sqrt_add_le_sqrt_add_sqrt (by positivity : 0 ≤ Δ * x) zero_le_one
          have h2 : 16 * (D : ℝ) ^ 2 = (4 * (D : ℝ)) ^ 2 := by ring
          rw [h2]; linarith
      _ = Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ) := by
          rw [Real.sqrt_mul hΔ0.le, Real.sqrt_one, Real.sqrt_sq (by positivity)]
  have hfac2 : Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) ≤
      Real.sqrt x * (1 + Real.log x) ^ 3 := by
    have h5le6 : (1 + Real.log x) ^ 5 ≤ (1 + Real.log x) ^ 6 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hsq6 : Real.sqrt ((1 + Real.log x) ^ 6) = (1 + Real.log x) ^ 3 := by
      rw [show (1 + Real.log x) ^ 6 = ((1 + Real.log x) ^ 3) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    calc Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2)
        ≤ Real.sqrt (x * (1 + Real.log x) ^ 5) := Real.sqrt_le_sqrt hL2
      _ ≤ Real.sqrt (x * (1 + Real.log x) ^ 6) := Real.sqrt_le_sqrt (by gcongr)
      _ = Real.sqrt x * (1 + Real.log x) ^ 3 := by rw [Real.sqrt_mul (by linarith), hsq6]
  have hprod_sqrt :
      Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) ≤
        (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by
    calc Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2)
        ≤ Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt hLS
      _ = Real.sqrt (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) := Real.sqrt_mul (by positivity) _
      _ ≤ (Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ)) * (Real.sqrt x * (1 + Real.log x) ^ 3) :=
          mul_le_mul hfac1 hfac2 (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt Δ * (Real.sqrt x * Real.sqrt x) + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) *
            (1 + Real.log x) ^ 3 := by ring
      _ = (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by
          rw [Real.mul_self_sqrt (by linarith)]
  rw [hLHS]
  calc ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖)
      ≤ Real.sqrt (∑ p ∈ S, w p) * Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) := hCS
    _ ≤ (2 * (D : ℝ)) * ((Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3) :=
        mul_le_mul hsqrtW hprod_sqrt (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by ring

/-- Upper bound on sub-interval count `blockCount N U V Δ r ≤ 3 / Δ` when `blockLo < blockHi`. -/
private lemma blockCount_le_three_div {N U V r : ℕ} {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (blockCount N U V Δ r : ℝ) ≤ 3 / Δ := by
  unfold blockCount
  set M := blockLo V r
  set M' := blockHi N U V r
  set h := blockStep V Δ r
  have hh1 : 1 ≤ h := le_max_left 1 _
  have hdiff_le : M' - M ≤ M := by
    dsimp only [M, M', blockLo, blockHi]
    have h1 : min (V * 2 ^ (r + 1)) (N / U) ≤ V * 2 ^ (r + 1) := Nat.min_le_left _ _
    have h2 : V * 2 ^ (r + 1) = V * 2 ^ r + V * 2 ^ r := by rw [pow_succ]; ring
    omega
  by_cases hh_eq1 : h = 1
  · have hfl_le1 : ⌊Δ * (M : ℝ)⌋₊ ≤ 1 := by
      have : ⌊Δ * (M : ℝ)⌋₊ ≤ h := le_max_right 1 _
      omega
    have hΔM_lt2 : Δ * (M : ℝ) < 2 := by
      have := Nat.lt_floor_add_one (Δ * (M : ℝ))
      have h1 : (⌊Δ * (M : ℝ)⌋₊ : ℝ) ≤ 1 := by exact_mod_cast hfl_le1
      linarith
    have hM_le : (M : ℝ) ≤ 2 / Δ := (le_div_iff₀ hΔ0).mpr (by linarith)
    have hnat : (M' - M + h - 1) / h = M' - M := by rw [hh_eq1]; simp
    rw [hnat]
    calc ((M' - M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hdiff_le
      _ ≤ 2 / Δ := hM_le
      _ ≤ 3 / Δ := div_le_div_of_nonneg_right (by norm_num) hΔ0.le
  · have hh_ge2 : 2 ≤ h := by omega
    have hh_eq : h = ⌊Δ * (M : ℝ)⌋₊ := by
      rcases le_total 1 ⌊Δ * (M : ℝ)⌋₊ with h1 | h1
      · exact max_eq_right h1
      · have hh1' : h = 1 := max_eq_left h1; omega
    have h2h_gt : Δ * (M : ℝ) < 2 * (h : ℝ) := by
      have h1 := Nat.lt_floor_add_one (Δ * (M : ℝ))
      rw [← hh_eq] at h1
      have h2 : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge2
      linarith
    have hdiv_le : (((M' - M + h - 1) / h : ℕ) : ℝ) ≤ (M : ℝ) / (h : ℝ) + 1 := by
      have hnum : M' - M + h - 1 ≤ M + h :=
        (Nat.sub_le (M' - M + h) 1).trans (Nat.add_le_add_right hdiff_le h)
      have hle1 : ((M' - M + h - 1) / h : ℕ) ≤ (M + h) / h := Nat.div_le_div_right hnum
      have hle2 : ((M + h) / h : ℕ) = M / h + 1 := Nat.add_div_right M (by omega)
      have h1 : (((M' - M + h - 1) / h : ℕ) : ℝ) ≤ ((M / h : ℕ) : ℝ) + 1 := by
        exact_mod_cast (hle1.trans_eq hle2)
      have h2 : ((M / h : ℕ) : ℝ) ≤ (M : ℝ) / (h : ℝ) := Nat.cast_div_le
      linarith
    have hMh : (M : ℝ) / (h : ℝ) ≤ 2 / Δ := by
      rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hΔ0]
      linarith
    have h1le : (1 : ℝ) ≤ 1 / Δ := (one_le_div hΔ0).mpr hΔ1.le
    have hadd : 2 / Δ + 1 / Δ = 3 / Δ := by ring
    linarith

open Classical in
/-- **Unconditional Bilinear Large-Sieve Bound on the Rectangular Part `vaughanS3Rect`**:
for `1 ≤ D`, `1 ≤ U`, `1 ≤ V`, `3 ≤ x`, `0 < Δ < 1`,
`∑_{q ≤ 2D} (q / φ(q)) ∑*_{χ mod q} ‖vaughanS3Rect χ U V x Δ‖ ≤ 120 * (x + D x / √U + D x / √(Δ V) + D² √x / √Δ) * (1 + log x)⁴`. -/
private lemma sum_vaughanS3Rect_le {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ ≤
      120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hU_pos : (0 : ℝ) < (U : ℝ) := Nat.cast_pos.mpr hU
  have hV_pos : (0 : ℝ) < (V : ℝ) := Nat.cast_pos.mpr hV
  set R : ℕ := Nat.log 2 ⌊x⌋₊ + 1
  -- Pull `(r, j)` sums outside via triangle inequality
  have htri :
      ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖vaughanS3Rect χ U V x Δ‖ ≤
        ∑ r ∈ Finset.range R,
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                      (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                   (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                      (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := by
    have hpt : ∀ k ∈ Finset.range (2 * D), ∀ χ : DirichletCharacter ℂ (k + 1),
        ‖vaughanS3Rect χ U V x Δ‖ ≤
          ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
             (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := fun _ _ χ => by
      unfold vaughanS3Rect
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    calc _ ≤ ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                    ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                        (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                     (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                        (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun χ _ => hpt k hk χ) (by positivity)
      _ = _ := by
            have h1 :
                ∑ k ∈ Finset.range (2 * D),
                    (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                        ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                          ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                              (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                           (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                              (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ =
                ∑ k ∈ Finset.range (2 * D),
                  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                    (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                        ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                            (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                         (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                            (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_comm, Finset.mul_sum]
            rw [h1, Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => Finset.sum_comm
  -- Bound each dyadic block `r < R`
  have hblock : ∀ r ∈ Finset.range R,
      ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                  (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
               (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                  (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ ≤
      28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3 := by
    intro r _
    set M := blockLo V r
    set M' := blockHi ⌊x⌋₊ U V r
    set h := blockStep V Δ r
    set L := blockCount ⌊x⌋₊ U V Δ r
    by_cases hM_ge : ⌊x⌋₊ / U ≤ M
    · have hM'_le : M' ≤ M := (Nat.min_le_right _ _).trans hM_ge
      have hL0 : L = 0 := by
        dsimp only [L, blockCount]
        have hsub : M' - M = 0 := Nat.sub_eq_zero_of_le hM'_le
        rw [hsub, zero_add]
        exact Nat.div_eq_of_lt (by have : 1 ≤ h := le_max_left 1 _; omega)
      rw [hL0, Finset.range_zero, Finset.sum_empty]
      positivity
    · push Not at hM_ge
      have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hV (by positivity))
      have hVM : (V : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right V (show 0 < 2 ^ r by positivity)
      have hMU : (M : ℝ) ≤ x / (U : ℝ) := by
        rw [le_div_iff₀ hU_pos]
        have h1 : M * U ≤ ⌊x⌋₊ := by
          have := (Nat.le_div_iff_mul_le hU).mp hM_ge.le
          exact this
        exact (by exact_mod_cast h1 : (M : ℝ) * (U : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
      have hNM_pos : 1 ≤ ⌊x⌋₊ / M := by
        have hM_le_N : M ≤ ⌊x⌋₊ := hM_ge.le.trans (Nat.div_le_self ⌊x⌋₊ U)
        exact Nat.div_pos hM_le_N (Nat.mul_pos hV (by positivity))
      have hstep_le : (h : ℝ) ≤ Δ * (M : ℝ) + 1 := by
        dsimp only [h, blockStep]
        rcases le_total 1 ⌊Δ * (M : ℝ)⌋₊ with h1 | h1
        · rw [max_eq_right h1]; linarith [Nat.floor_le (by positivity : 0 ≤ Δ * (M : ℝ))]
        · rw [max_eq_left h1]; norm_num; positivity
      -- Per-`j` bound via `bilinear_multiplicative_large_sieve`
      have hper_j : ∀ j ∈ Finset.range L,
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                    (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                 (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                    (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ ≤
          Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
            Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
            Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) *
            Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) := by
        intro j _
        have hbls := bilinear_multiplicative_large_sieve (2 * D)
          (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j) U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)
          (fun m => (Λ m : ℂ)) (fun n => (vaughanMollifier U n : ℂ))
        have hlen_m : ((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) ≤ Δ * (M : ℝ) + 1 := by
          have h1 : subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j ≤ h := by
            dsimp only [subHi, subLo]
            have hle1 : min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi ⌊x⌋₊ U V r) ≤
                blockLo V r + (j + 1) * blockStep V Δ r := Nat.min_le_left _ _
            have hmul : blockLo V r + (j + 1) * blockStep V Δ r =
                blockLo V r + j * blockStep V Δ r + blockStep V Δ r := by ring
            have h2 : min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi ⌊x⌋₊ U V r) -
                (blockLo V r + j * blockStep V Δ r) ≤ blockStep V Δ r := by omega
            exact h2
          exact (by exact_mod_cast h1 : ((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) ≤ (h : ℝ)).trans hstep_le
        have hM_le_b : M ≤ subHi ⌊x⌋₊ U V Δ r j := by
          unfold subHi
          apply le_min
          · exact Nat.le_add_right M _
          · unfold blockHi
            apply le_min
            · exact Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ r))
            · exact hM_ge.le
        have hdiv_le : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j ≤ ⌊x⌋₊ / M :=
          Nat.div_le_div_left hM_le_b (Nat.mul_pos hV (by positivity))
        have hNM_le_R : ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ x / (M : ℝ) := by
          calc ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / (M : ℝ) := Nat.cast_div_le
            _ ≤ x / (M : ℝ) := div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) hM_pos.le
        have hlen_n : ((⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U : ℕ) : ℝ) ≤ x / (M : ℝ) := by
          have h1 : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U ≤ ⌊x⌋₊ / M := (Nat.sub_le _ _).trans hdiv_le
          exact (by exact_mod_cast h1 : _ ≤ ((⌊x⌋₊ / M : ℕ) : ℝ)).trans hNM_le_R
        have hL2_m :
            ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), ‖(Λ m : ℂ)‖ ^ 2 =
              ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2 :=
          Finset.sum_congr rfl fun m _ => by
            rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hL2_n :
            ∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), ‖(vaughanMollifier U n : ℂ)‖ ^ 2 ≤
              (x / (M : ℝ)) * (1 + Real.log x) ^ 3 := by
          have hsub : Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) ⊆ Finset.Icc 1 (⌊x⌋₊ / M) := by
            intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
          calc ∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), ‖(vaughanMollifier U n : ℂ)‖ ^ 2
              ≤ ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / M), ‖(vaughanMollifier U n : ℂ)‖ ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
            _ ≤ ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / M), (n.divisors.card : ℝ) ^ 2 := by
                refine Finset.sum_le_sum fun n _ => ?_
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (abs_vaughanMollifier_le_divisors U n) 2
            _ ≤ ((⌊x⌋₊ / M : ℕ) : ℝ) * (1 + Real.log ((⌊x⌋₊ / M : ℕ) : ℝ)) ^ 3 :=
                Stage10ZeroDensity.sum_divisors_card_sq_le hNM_pos
            _ ≤ (x / (M : ℝ)) * (1 + Real.log x) ^ 3 := by
                have hlog_le : Real.log ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ Real.log x := by
                  refine Real.log_le_log (Nat.cast_pos.mpr hNM_pos) ?_
                  exact (by exact_mod_cast Nat.div_le_self ⌊x⌋₊ M : _ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
                have hnn : 0 ≤ 1 + Real.log ((⌊x⌋₊ / M : ℕ) : ℝ) := by
                  have := Real.log_natCast_nonneg (⌊x⌋₊ / M); linarith
                gcongr
        have h3Q2 : 3 * ((2 * D : ℕ) : ℝ) ^ 2 = 12 * (D : ℝ) ^ 2 := by push_cast; ring
        refine hbls.trans ?_
        rw [h3Q2, hL2_m]
        have h1 : Real.sqrt (((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) + 12 * (D : ℝ) ^ 2) ≤
            Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have h2 : Real.sqrt (((⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U : ℕ) : ℝ) + 12 * (D : ℝ) ^ 2) ≤
            Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have h3 := Real.sqrt_le_sqrt hL2_n
        have hmul12 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have hmul123 := mul_le_mul hmul12 h3 (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        have hmul1234 := mul_le_mul_of_nonneg_right hmul123
          (Real.sqrt_nonneg (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2))
        linarith
      -- Sum over `j ∈ range L` using Cauchy–Schwarz on `∑ √(s_j)`
      have hsum_j :
          ∑ j ∈ Finset.range L,
            Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) ≤
          Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x) := by
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L)
          (fun _ => (1 : ℝ))
          (fun j => Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2))
        simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hCS
        have hsq_sum :
            ∑ j ∈ Finset.range L,
              (Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)) ^ 2 =
            ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 := by
          have h1 : ∀ j ∈ Finset.range L,
              (Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)) ^ 2 =
                ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2 :=
            fun j _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [Finset.sum_congr rfl h1]
          exact (sum_Ioc_uniform M M' h L (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r) _).symm
        rw [hsq_sum] at hCS
        have hM_L2 : ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 ≤ (M : ℝ) * (Real.log x) ^ 2 := by
          calc ∑ m ∈ Finset.Ioc M M', Λ m ^ 2
              ≤ ∑ _m ∈ Finset.Ioc M M', (Real.log x) ^ 2 := by
                refine Finset.sum_le_sum fun m hm => ?_
                have hm1 : 1 ≤ m := by
                  have := (Finset.mem_Ioc.mp hm).1
                  have : 1 ≤ M := Nat.mul_pos hV (by positivity); omega
                have hmx : (m : ℝ) ≤ x := by
                  have h1 : m ≤ ⌊x⌋₊ := ((Finset.mem_Ioc.mp hm).2.trans (Nat.min_le_right _ _)).trans
                    (Nat.div_le_self ⌊x⌋₊ U)
                  exact (by exact_mod_cast h1 : (m : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
                exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
                  (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hm1) hmx)) 2
            _ = ((Finset.Ioc M M').card : ℝ) * (Real.log x) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (M : ℝ) * (Real.log x) ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                rw [Nat.card_Ioc]
                have hle : M' - M ≤ M := by
                  dsimp only [M, M', blockLo, blockHi]
                  have h1 : min (V * 2 ^ (r + 1)) (⌊x⌋₊ / U) ≤ V * 2 ^ (r + 1) := Nat.min_le_left _ _
                  have h2 : V * 2 ^ (r + 1) = V * 2 ^ r + V * 2 ^ r := by rw [pow_succ]; ring
                  omega
                exact_mod_cast hle
        have hprod : (L : ℝ) * ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 ≤ (3 / Δ) * ((M : ℝ) * (Real.log x) ^ 2) :=
          mul_le_mul (blockCount_le_three_div hΔ0 hΔ1) hM_L2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        calc ∑ j ∈ Finset.range L,
              Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)
            ≤ Real.sqrt ((3 / Δ) * ((M : ℝ) * (Real.log x) ^ 2)) :=
              Real.le_sqrt_of_sq_le (hCS.trans hprod)
          _ = Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hM_pos.le, Real.sqrt_sq hlogx_nn]
      -- Simplify the algebraic product
      have hA_fac : Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) ≤
          2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ := by
        have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        have hEq : (3 / Δ) * (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) =
            3 * (M : ℝ) + (3 + 36 * (D : ℝ) ^ 2) / Δ := by field_simp [hΔ0.ne']; ring
        have hle : 3 * (M : ℝ) + (3 + 36 * (D : ℝ) ^ 2) / Δ ≤
            4 * (M : ℝ) + 49 * (D : ℝ) ^ 2 / Δ := by
          have h1 : 3 + 36 * (D : ℝ) ^ 2 ≤ 49 * (D : ℝ) ^ 2 := by nlinarith
          have h2 : (3 + 36 * (D : ℝ) ^ 2) / Δ ≤ 49 * (D : ℝ) ^ 2 / Δ :=
            div_le_div_of_nonneg_right h1 hΔ0.le
          linarith
        calc Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)
            = Real.sqrt ((3 / Δ) * (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)) :=
              (Real.sqrt_mul (by positivity) _).symm
          _ ≤ Real.sqrt (4 * (M : ℝ) + 49 * (D : ℝ) ^ 2 / Δ) := by
              rw [hEq]; exact Real.sqrt_le_sqrt hle
          _ ≤ Real.sqrt (4 * (M : ℝ)) + Real.sqrt (49 * (D : ℝ) ^ 2 / Δ) :=
              sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
          _ = 2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
                  show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
                  Real.sqrt_div (by positivity),
                  show 49 * (D : ℝ) ^ 2 = (7 * (D : ℝ)) ^ 2 by ring,
                  Real.sqrt_sq (by positivity)]
      have hB_fac : Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) ≤
          Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ) := by
        calc Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2)
            ≤ Real.sqrt (x / (M : ℝ) + 16 * (D : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ ≤ Real.sqrt (x / (M : ℝ)) + Real.sqrt (16 * (D : ℝ) ^ 2) :=
              sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
          _ = Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ) := by
              rw [show 16 * (D : ℝ) ^ 2 = (4 * (D : ℝ)) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have hC_fac : Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) ≤
          Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2 := by
        have h34 : (1 + Real.log x) ^ 3 ≤ (1 + Real.log x) ^ 4 :=
          pow_le_pow_right₀ (by linarith) (by omega)
        calc Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)
            ≤ Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 4) := Real.sqrt_le_sqrt (by gcongr)
          _ = Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2 := by
              rw [Real.sqrt_mul (by positivity),
                  show (1 + Real.log x) ^ 4 = ((1 + Real.log x) ^ 2) ^ 2 by ring,
                  Real.sqrt_sq (by positivity)]
      have hlog_prod : Real.log x * (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 3 := by
        have : Real.log x ≤ 1 + Real.log x := by linarith
        nlinarith [sq_nonneg (1 + Real.log x)]
      -- Combine the four cross-terms
      have hcross :
          (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
            ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ))) ≤
          28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
            (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
            (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) := by
        have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM_pos.le
        have hsqxM : Real.sqrt (x / (M : ℝ)) * Real.sqrt (x / (M : ℝ)) = x / (M : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hsq_prod : Real.sqrt (M : ℝ) * Real.sqrt (x / (M : ℝ)) = Real.sqrt x := by
          rw [← Real.sqrt_mul hM_pos.le, mul_div_cancel₀ x hM_pos.ne']
        have hterm1 : (M : ℝ) * (x / (M : ℝ)) = x := mul_div_cancel₀ x hM_pos.ne'
        have hterm2 : (M : ℝ) * Real.sqrt (x / (M : ℝ)) ≤ x / Real.sqrt (U : ℝ) := by
          have h1 : (M : ℝ) * Real.sqrt (x / (M : ℝ)) = Real.sqrt (M : ℝ) * Real.sqrt x := by
            rw [← hsq_prod, ← mul_assoc, hsqM]
          rw [h1]
          have h2 : Real.sqrt (M : ℝ) ≤ Real.sqrt x / Real.sqrt (U : ℝ) := by
            rw [← Real.sqrt_div (by linarith)]
            exact Real.sqrt_le_sqrt hMU
          calc Real.sqrt (M : ℝ) * Real.sqrt x
              ≤ (Real.sqrt x / Real.sqrt (U : ℝ)) * Real.sqrt x :=
                mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
            _ = (Real.sqrt x * Real.sqrt x) / Real.sqrt (U : ℝ) := by ring
            _ = x / Real.sqrt (U : ℝ) := by rw [Real.mul_self_sqrt (by linarith)]
        have hterm3 : (Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ)) ≤
            x / Real.sqrt (Δ * (V : ℝ)) := by
          have hEq : (Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ)) =
              x / (Real.sqrt Δ * Real.sqrt (M : ℝ)) := by
            have hne : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hM_pos).ne'
            have hneΔ : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
            field_simp [hne, hneΔ, hM_pos.ne']
            exact Real.sq_sqrt hM_pos.le
          rw [hEq, Real.sqrt_mul hΔ0.le]
          exact div_le_div_of_nonneg_left (by linarith)
            (mul_pos (Real.sqrt_pos.mpr hΔ0) (Real.sqrt_pos.mpr hV_pos))
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVM) (Real.sqrt_nonneg _))
        have hexpand :
            (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ))) =
            2 * ((M : ℝ) * (x / (M : ℝ))) +
            8 * (D : ℝ) * ((M : ℝ) * Real.sqrt (x / (M : ℝ))) +
            7 * (D : ℝ) * ((Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ))) +
            28 * (D : ℝ) ^ 2 * ((Real.sqrt (M : ℝ) * Real.sqrt (x / (M : ℝ))) / Real.sqrt Δ) := by
          have h1 : (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) =
              2 * (M : ℝ) + 7 * (D : ℝ) * (Real.sqrt (M : ℝ) / Real.sqrt Δ) := by
            rw [add_mul, mul_assoc, hsqM]; ring
          have h2 : (Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ)) =
              x / (M : ℝ) + 4 * (D : ℝ) * Real.sqrt (x / (M : ℝ)) := by
            rw [add_mul, hsqxM]
          rw [h1, h2]; ring
        rw [hexpand, hterm1, hsq_prod]
        have h2' := mul_le_mul_of_nonneg_left hterm2 (show 0 ≤ 8 * (D : ℝ) by positivity)
        have h3' := mul_le_mul_of_nonneg_left hterm3 (show 0 ≤ 7 * (D : ℝ) by positivity)
        have hx_nn : 0 ≤ x := by linarith
        have hU_nn : 0 ≤ (D : ℝ) * x / Real.sqrt (U : ℝ) := by positivity
        have hV_nn : 0 ≤ (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) := by positivity
        have hD_nn : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ := by positivity
        have h2'' : 8 * (D : ℝ) * (x / Real.sqrt (U : ℝ)) = 8 * ((D : ℝ) * x / Real.sqrt (U : ℝ)) := by ring
        have h3'' : 7 * (D : ℝ) * (x / Real.sqrt (Δ * (V : ℝ))) = 7 * ((D : ℝ) * x / Real.sqrt (Δ * (V : ℝ))) := by ring
        have h4'' : 28 * (D : ℝ) ^ 2 * (Real.sqrt x / Real.sqrt Δ) = 28 * ((D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) := by ring
        linarith
      calc ∑ j ∈ Finset.range L,
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                      (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                   (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                      (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖
          ≤ ∑ j ∈ Finset.range L,
              Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
                Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
                Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) *
                Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) :=
            Finset.sum_le_sum hper_j
        _ = (Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
              Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
              Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) *
            ∑ j ∈ Finset.range L,
              Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
              Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
              Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) *
            (Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x)) :=
            mul_le_mul_of_nonneg_left hsum_j (by positivity)
        _ = (Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)) *
              Real.sqrt (M : ℝ) *
              (Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
               Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) * Real.log x := by ring
        _ ≤ (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) *
              Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) *
               (Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2)) * Real.log x := by
            gcongr
        _ = ((2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ)))) *
            (Real.log x * (1 + Real.log x) ^ 2) := by ring
        _ ≤ (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
              (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
              (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ)) * (1 + Real.log x) ^ 3 :=
            mul_le_mul hcross hlog_prod (by positivity) (by positivity)
  -- Sum over `r ∈ Finset.range R` using `R = Nat.log 2 ⌊x⌋₊ + 1 ≤ 4 * (1 + log x)`
  have hR_le : (R : ℝ) ≤ 4 * (1 + Real.log x) := by
    have hpow : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by
      have : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
      omega)
    have hpowR : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x :=
      (by exact_mod_cast hpow : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊) hpowR
    rw [Real.log_pow] at hlog
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hnat : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ 2 * Real.log x := by nlinarith
    dsimp only [R]; push_cast; linarith
  calc _ ≤ ∑ _r ∈ Finset.range R,
            28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
              (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
              (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3 :=
          htri.trans (Finset.sum_le_sum hblock)
    _ = (R : ℝ) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (4 * (1 + Real.log x)) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_right hR_le (by positivity)
    _ ≤ 120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by
        have hnn : 0 ≤ (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by positivity
        have hEq : (4 * (1 + Real.log x)) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) =
          112 * ((x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4) := by ring
        rw [hEq]; linarith

open Classical in
/-- **Master Unconditional Dyadic Primitive-Character Average Bound (Vaughan + Pólya–Vinogradov + Large Sieve)**:
for ALL `1 ≤ D`, `1 ≤ U`, `1 ≤ V`, `3 ≤ x`, `0 < Δ < 1`, `(D : ℝ) ≤ x`, `(V : ℝ) ≤ x`:
`∑_{D < d ≤ 2D} (1 / φ(d)) ∑*_{χ mod d} ‖ψ(x, χ)‖ ≤ 180 * (D V + U V D^{3/2} + x/D + x/√U + x/√(Δ V) + D √x / √Δ + √Δ x + √x + D √x) * (1 + log x)⁴`. -/
theorem dyadic_prim_chebyshevPsiChar_bound {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hDx : (D : ℝ) ≤ x) (hVx : (V : ℝ) ≤ x)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.Ico D (2 * D),
        (1 / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      180 * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
  have hx1 : 1 ≤ x := by linarith
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL_ge1 : 1 ≤ 1 + Real.log x := by linarith
  -- Step 1: `1 / φ(k+1) ≤ (1 / D) * ((k+1) / φ(k+1))` on `k ∈ Ico D (2 * D)`
  have hstep1 :
      ∑ k ∈ Finset.Ico D (2 * D),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.Ico D (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkD : D ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
    have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
    have hfac : 1 / (Nat.totient (k + 1) : ℝ) ≤
        (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) := by
      have h1 : (D : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hkD
      rw [show (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) =
        (((k + 1 : ℕ) : ℝ) / (D : ℝ)) * (1 / (Nat.totient (k + 1) : ℝ)) by ring]
      exact le_mul_of_one_le_left (by positivity) ((one_le_div hD_pos).mpr h1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  -- Step 2: Apply Vaughan decomposition `ψ(x, χ) = S₀ + S₁ - S₂ - S₃Rect - S₃Bdy`
  have hsplit :
      ∑ k ∈ Finset.Ico D (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖)) +
        (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖) +
        (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖) := by
    have hsub : Finset.Ico D (2 * D) ⊆ Finset.range (2 * D) := by
      intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; exact hk.2
    have hR_mono :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ ≤
        ∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hB_mono :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ ≤
        ∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hpt :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) +
             ‖vaughanS3Rect χ U V x Δ‖ + ‖vaughanS3Bdy χ U V x Δ‖) := by
      refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) (by positivity)
      rw [chebyshevPsiChar_vaughan_decomp χ hU hx1, vaughanS3_eq_rect_add_bdy χ hU hV x Δ]
      have h1 := norm_sub_le (vaughanS0 χ V x + vaughanS1 χ U x - vaughanS2 χ U V x)
        (vaughanS3Rect χ U V x Δ + vaughanS3Bdy χ U V x Δ)
      have h2 := norm_sub_le (vaughanS0 χ V x + vaughanS1 χ U x) (vaughanS2 χ U V x)
      have h3 := norm_add_le (vaughanS0 χ V x) (vaughanS1 χ U x)
      have h4 := norm_add_le (vaughanS3Rect χ U V x Δ) (vaughanS3Bdy χ U V x Δ)
      linarith
    have hpt_eq :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) +
             ‖vaughanS3Rect χ U V x Δ‖ + ‖vaughanS3Bdy χ U V x Δ‖) =
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖)) +
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖) +
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [hpt_eq] at hpt
    linarith
  -- Step 3: Bound the Type 0 + Type I sum
  have hT01 :
      ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) ≤
      48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) *
        (1 + Real.log x) ^ 4 := by
    have hlog2D : 1 + Real.log (2 * (D : ℝ)) ≤ 2 * (1 + Real.log x) := by
      have h1 : Real.log (2 * (D : ℝ)) = Real.log 2 + Real.log (D : ℝ) :=
        Real.log_mul (by norm_num) hD_pos.ne'
      have h2 : Real.log (D : ℝ) ≤ Real.log x := Real.log_le_log hD_pos hDx
      have h3 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hsqrt2D : Real.sqrt (2 * (D : ℝ)) ≤ 2 * Real.sqrt (D : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hsq2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _)
    set M01 : ℝ := (V : ℝ) * Real.log x +
      (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x
    have hpt01 : ∀ k ∈ Finset.Ico D (2 * D),
        ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖ ≤ M01 := by
      intro k hk χ hχ
      have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
      have hk2 : 2 ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
      have hk_le : ((k + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
        have := (Finset.mem_Ico.mp hk).2; exact_mod_cast (by omega : k + 1 ≤ 2 * D)
      have hsqk : Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (D : ℝ) :=
        (Real.sqrt_le_sqrt hk_le).trans hsqrt2D
      have hlogk : 1 + Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log x) := by
        have hlk := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) hk_le
        linarith
      have h0 := norm_vaughanS0_le χ V hx1
      have h1 := norm_vaughanS1_le hk2 hprim U hx1
      have h2 := norm_vaughanS2_le (U := U) hk2 hprim hx1 hVx
      have hprod_le : Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) :=
        mul_le_mul hsqk hlogk (by have := Real.log_natCast_nonneg (k + 1); linarith) (by positivity)
      have h1' : 2 * (U : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) * Real.log x ≤
          2 * (U : ℝ) * ((2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x))) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hprod_le (show 0 ≤ 2 * (U : ℝ) by positivity)
        have := mul_le_mul_of_nonneg_right this hlogx_nn
        linarith
      have h2' : (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (U : ℝ) * (V : ℝ) * ((2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x))) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hprod_le (show 0 ≤ (U : ℝ) * (V : ℝ) * Real.log x by positivity)
        linarith
      dsimp only [M01]; linarith
    have hM01_le : M01 ≤ 12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by
      have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
      have hUV : 2 * (U : ℝ) + (U : ℝ) * (V : ℝ) ≤ 3 * ((U : ℝ) * (V : ℝ)) := by nlinarith
      have hL1 : Real.log x ≤ 1 + Real.log x := by linarith
      have hL12 : Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
      have hL2 : (1 + Real.log x) * Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
      have h1 : (V : ℝ) * Real.log x ≤ (V : ℝ) * (1 + Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left hL12 (Nat.cast_nonneg _)
      have h2 : (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x ≤
          12 * ((U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by
        have hEq : (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x =
            4 * (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * Real.sqrt (D : ℝ) * ((1 + Real.log x) * Real.log x) := by ring
        rw [hEq]
        have ha : 4 * (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * Real.sqrt (D : ℝ) ≤
            12 * ((U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) := by nlinarith [Real.sqrt_nonneg (D : ℝ)]
        exact mul_le_mul ha hL2 (by positivity) (by positivity)
      dsimp only [M01]
      have hVnn : 0 ≤ (V : ℝ) * (1 + Real.log x) ^ 2 := by positivity
      linarith
    have hsum_le :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) ≤
        ((2 * D : ℕ) : ℝ) ^ 2 * M01 := by
      have hsub : Finset.Ico D (2 * D) ⊆ Finset.range (2 * D) := by
        intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      calc _ ≤ ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive), M01 :=
              Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun χ hχ => hpt01 k hk χ hχ) (by positivity)
        _ = (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)) * M01 := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)) * M01 :=
              mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
                (by dsimp only [M01]; positivity)
        _ ≤ ((2 * D : ℕ) : ℝ) ^ 2 * M01 :=
              mul_le_mul_of_nonneg_right (sum_prim_weight_le (2 * D)) (by dsimp only [M01]; positivity)
    have hL24 : (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 4 := pow_le_pow_right₀ hL_ge1 (by omega)
    calc _ ≤ ((2 * D : ℕ) : ℝ) ^ 2 * M01 := hsum_le
      _ ≤ (4 * (D : ℝ) ^ 2) * (12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2) := by
          have hcast : ((2 * D : ℕ) : ℝ) ^ 2 = 4 * (D : ℝ) ^ 2 := by push_cast; ring
          rw [hcast]; exact mul_le_mul_of_nonneg_left hM01_le (by positivity)
      _ ≤ 48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) *
            (1 + Real.log x) ^ 4 := by
          have hEq : (4 * (D : ℝ) ^ 2) * (12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2) =
              48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by ring
          rw [hEq]
          exact mul_le_mul_of_nonneg_left hL24 (by positivity)
  -- Step 4: Combine Type 0 + Type I + Type II (Rect + Bdy) and divide by `D`
  have hRect := sum_vaughanS3Rect_le hD hU hV hx hΔ0 hΔ1
  have hBdy := sum_vaughanS3Bdy_le hD hU hV hx hΔ0 hΔ1
  have hL34 : (1 + Real.log x) ^ 3 ≤ (1 + Real.log x) ^ 4 := pow_le_pow_right₀ hL_ge1 (by omega)
  have hBdy' :
      2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 ≤
      8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
    have h1 : 2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) ≤
        8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) := by
      have : 0 ≤ (D : ℝ) * Real.sqrt Δ * x := by positivity
      have : 0 ≤ (D : ℝ) * Real.sqrt x := by positivity
      linarith
    exact mul_le_mul h1 hL34 (by positivity) (by positivity)
  refine hstep1.trans ?_
  have hsum_comb :
      ∑ k ∈ Finset.Ico D (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
    have hD_cancel : (D : ℝ) * (x / (D : ℝ)) = x := mul_div_cancel₀ x hD_pos.ne'
    have h1 :
        48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) +
        120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) + (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) +
        8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) ≤
        180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) := by
      have ha : 0 ≤ (D : ℝ) ^ 2 * (V : ℝ) := by positivity
      have hb : 0 ≤ (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ) := by positivity
      have hc : 0 ≤ x := by linarith
      have hd : 0 ≤ (D : ℝ) * x / Real.sqrt (U : ℝ) := by positivity
      have he : 0 ≤ (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) := by positivity
      have hf : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ := by positivity
      have hg : 0 ≤ (D : ℝ) * Real.sqrt Δ * x := by positivity
      have hh : 0 ≤ (D : ℝ) * Real.sqrt x := by positivity
      have hi : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x := by positivity
      have hR_exp : 180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) =
          180 * ((D : ℝ) ^ 2 * (V : ℝ)) + 180 * ((U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) +
          180 * ((D : ℝ) * (x / (D : ℝ))) + 180 * ((D : ℝ) * x / Real.sqrt (U : ℝ)) +
          180 * ((D : ℝ) * x / Real.sqrt (Δ * (V : ℝ))) + 180 * ((D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) +
          180 * ((D : ℝ) * Real.sqrt Δ * x) + 180 * ((D : ℝ) * Real.sqrt x) +
          180 * ((D : ℝ) ^ 2 * Real.sqrt x) := by ring
      rw [hR_exp, hD_cancel]
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (1 + Real.log x) ^ 4 by positivity)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum_comb (show 0 ≤ 1 / (D : ℝ) by positivity)
  refine hmul.trans_eq ?_
  field_simp [hD_pos.ne']

/-! ## Section 4: Unconditional Full Bombieri–Vinogradov Theorem (`ϑ = 1/2`) -/

/-- Maximum AP prime-power error `max_{a < q, (a, q) = 1} |ψ(x; q, a) - x / φ(q)|`. -/
def psiAPMaxError (q : ℕ) (x : ℝ) : ℝ :=
  if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
      (fun a => |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)|)
  else 0

theorem psiAPMaxError_nonneg (q : ℕ) (x : ℝ) : 0 ≤ psiAPMaxError q x := by
  unfold psiAPMaxError
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact (abs_nonneg _).trans (Finset.le_sup' (f := fun a =>
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)|) ha)
  · exact le_rfl

/-- `chebyshevPsiAP q a x` depends only on `a % q`. -/
private lemma chebyshevPsiAP_mod (q a : ℕ) (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiAP q a x = Stage2DirichletAP.chebyshevPsiAP q (a % q) x := by
  unfold Stage2DirichletAP.chebyshevPsiAP
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff : n ≡ a [MOD q] ↔ n ≡ a % q [MOD q] := by
    simp [Nat.ModEq]
  by_cases h : n ≡ a [MOD q]
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- For every `q ≥ 1` and every `a` coprime to `q`, `|ψ(x; q, a) - x / φ(q)| ≤ psiAPMaxError q x`. -/
theorem abs_chebyshevPsiAP_sub_le_psiAPMaxError {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    (x : ℝ) :
    |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ psiAPMaxError q x := by
  have hmem : a % q ∈ (Finset.range q).filter (fun b => Nat.Coprime b q) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hq), ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hcop.gcd_eq_one
  unfold psiAPMaxError
  rw [dif_pos ⟨a % q, hmem⟩, chebyshevPsiAP_mod q a x]
  exact Finset.le_sup' (f := fun b =>
    |Stage2DirichletAP.chebyshevPsiAP q b x - x / (q.totient : ℝ)|) hmem

/-- Upper-bound characterization of `psiAPMaxError q x`. -/
theorem psiAPMaxError_le_of_forall {q : ℕ} {x M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a : ℕ, Nat.Coprime a q →
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ M) :
    psiAPMaxError q x ≤ M := by
  unfold psiAPMaxError
  split_ifs with hne
  · refine Finset.sup'_le hne _ fun a ha => h a (Finset.mem_filter.mp ha).2
  · exact hM

open Classical in
/-- Per-modulus reduction of `psiAPMaxError q x` to primitive characters of conductor `3 ≤ d ∣ q`. -/
private lemma psiAPMaxError_le_prim_divisors {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q)
    {x : ℝ} (hx : 3 ≤ x) (hQx : (Q : ℝ) ≤ x) :
    psiAPMaxError q x ≤
      (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Real.log x) ^ 2 +
      (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
  have hq1 : 1 ≤ q := NeZero.pos q
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1)
  have hRHS_nn : 0 ≤
      (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Real.log x) ^ 2 +
      (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hsum_nn : 0 ≤ ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  refine psiAPMaxError_le_of_forall hRHS_nn fun a hcop => ?_
  rw [Stage2DirichletAP.chebyshevPsiAP_eq_principal_add_nonprincipal_re hcop x]
  have hsplit_eq :
      Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re -
          x / (q.totient : ℝ) =
      (q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x) +
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re := by
    ring
  rw [hsplit_eq]
  -- Principal part bound
  have hlogq : Real.log (q : ℝ) ≤ Real.log x :=
    Real.log_le_log (Nat.cast_pos.mpr hq1) ((by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQx)
  have hprinc : |Stage2DirichletAP.chebyshevPsiCoprime q x - x| ≤
      |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2 := by
    have hcop_bd := Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_le_log hq1 hx1
    have hcop_nn := (Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_bounds hq1 hx1).1
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiff_le : RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x ≤
        2 * (Real.log x) ^ 2 := by
      have h1 : Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log x := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]; nlinarith
      calc RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x
          ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := hcop_bd
        _ ≤ (2 * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right h1 hlogx_nn
        _ = 2 * (Real.log x) ^ 2 := by ring
    have heq : Stage2DirichletAP.chebyshevPsiCoprime q x - x =
        (RHDirect.chebyshevPsi x - x) - (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) := by
      ring
    rw [heq]
    calc |(RHDirect.chebyshevPsi x - x) - (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x)|
        ≤ |RHDirect.chebyshevPsi x - x| + |RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x| :=
          abs_sub _ _
      _ = |RHDirect.chebyshevPsi x - x| + (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) := by
          rw [abs_of_nonneg hcop_nn]
      _ ≤ |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2 := by linarith
  -- Non-principal character transfer to primitive characters
  have hnonprinc :
      |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
        (q.totient : ℝ) * (Real.log x) ^ 2 +
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hstep1 :
        |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ + (Real.log x) ^ 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun χ hχ => ?_)
      have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      have hre : |(starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
        calc |(starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re|
            ≤ ‖starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x‖ :=
              Complex.abs_re_le_norm _
          _ = ‖χ (a : ZMod q)‖ * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
              rw [norm_mul, Complex.norm_conj]
          _ ≤ 1 * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ :=
              mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ = ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := one_mul _
      have htr := Stage8BarbanDavenport.norm_chebyshevPsiChar_sub_primitive_le hχne hx1
      have hdiff : ‖Stage2DirichletAP.chebyshevPsiChar χ x -
          Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤ (Real.log x) ^ 2 := by
        calc _ ≤ Real.log (q : ℝ) * Real.log x := htr
          _ ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_right hlogq hlogx_nn
          _ = (Real.log x) ^ 2 := by ring
      have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ +
            ‖Stage2DirichletAP.chebyshevPsiChar χ x -
              Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ := by
        simpa using norm_add_le (Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
          (Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
      linarith
    -- Re-index `χ ↦ ⟨χ.conductor, χ.primitiveCharacter⟩` injectively
    set target : Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
      ((Finset.Icc 3 Q).filter (fun d => d ∣ q)).sigma fun d =>
        Finset.univ.filter fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive
    let toPrim : DirichletCharacter ℂ q → (Σ d : ℕ, DirichletCharacter ℂ d) :=
      fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
    let induceFrom : (Σ d : ℕ, DirichletCharacter ℂ d) → DirichletCharacter ℂ q :=
      fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1
    have hind_eq : ∀ χ : DirichletCharacter ℂ q, induceFrom (toPrim χ) = χ := fun χ => by
      dsimp only [induceFrom, toPrim]
      rw [dif_pos χ.conductor_dvd_level, χ.changeLevel_primitiveCharacter]
    have hinj : Set.InjOn toPrim ((Finset.univ.erase (1 : DirichletCharacter ℂ q)) : Set (DirichletCharacter ℂ q)) := by
      intro χ₁ _ χ₂ _ h
      rw [← hind_eq χ₁, ← hind_eq χ₂, h]
    have hmaps : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), toPrim χ ∈ target := by
      intro χ hχ
      have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      have hd3 : 3 ≤ χ.conductor := Stage8BarbanDavenport.three_le_conductor_of_ne_one hχne
      have hdq : χ.conductor ∣ q := χ.conductor_dvd_level
      have hdle : χ.conductor ≤ Q := (Nat.le_of_dvd hq1 hdq).trans hqQ
      simp only [target, toPrim, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_univ, true_and]
      exact ⟨⟨⟨hd3, hdle⟩, hdq⟩, χ.primitiveCharacter_isPrimitive⟩
    have hprim_sum :
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
      have hsig :
          ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ =
            ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := Finset.sum_sigma _ _ _
      rw [← hsig]
      calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar (toPrim χ).2 x‖
          = ∑ p ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).image toPrim,
              ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ :=
            (Finset.sum_image (f := fun p : Σ d : ℕ, DirichletCharacter ℂ d =>
              ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖) hinj).symm
        _ ≤ ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
              fun _ _ _ => norm_nonneg _
    have hcard_le : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
      have htot : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have hnat : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
        calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card (Finset.erase_subset _ _)
          _ = q.totient := by rw [Finset.card_univ, htot]
      exact_mod_cast hnat
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hstep1
    have herr := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg (Real.log x))
    linarith
  -- Combine principal and non-principal parts
  have h1 : |(q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x) +
      (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
      (q.totient : ℝ)⁻¹ * |Stage2DirichletAP.chebyshevPsiCoprime q x - x| +
      (q.totient : ℝ)⁻¹ * |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| := by
    calc _ ≤ |(q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x)| +
            |(q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hphi_pos)]
  have h2 := mul_le_mul_of_nonneg_left hprinc (inv_nonneg.mpr hphi_pos.le)
  have h3 := mul_le_mul_of_nonneg_left hnonprinc (inv_nonneg.mpr hphi_pos.le)
  have hcancel : (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * (Real.log x) ^ 2 +
      ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖) =
      (Real.log x) ^ 2 + (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hphi_pos.ne', one_mul]
  linarith

open Classical in
/-- **Summed Reduction of `∑_{q ≤ Q} max_{(a,q)=1} |ψ(x; q, a) - x / φ(q)|` to Primitive Characters**:
for ALL `1 ≤ Q ≤ x` and `x ≥ 3`. -/
private lemma sum_psiAPMaxError_le_prim_sum {Q : ℕ} (hQ : 1 ≤ Q) {x : ℝ} (hx : 3 ≤ x)
    (hQx : (Q : ℝ) ≤ x) :
    ∑ q ∈ Finset.Icc 1 Q, psiAPMaxError q x ≤
      12 * Real.log x * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Q : ℝ) * (Real.log x) ^ 2 +
      12 * Real.log x *
        ∑ k ∈ Finset.Ico 2 Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log x := by
    have hle : 2 * (Q : ℝ) ≤ x ^ 2 := by nlinarith
    calc Real.log (2 * (Q : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hsum_inv : ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ ≤ 12 * Real.log x := by
    calc ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹
        ≤ 6 * Real.log (2 * (Q : ℝ)) := Stage8BarbanDavenport.sum_inv_totient_le_log hQ
      _ ≤ 12 * Real.log x := by linarith
  have hper : ∀ q ∈ Finset.Icc 1 Q,
      psiAPMaxError q x ≤
        (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
        (Real.log x) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have : NeZero q := ⟨by omega⟩
    exact psiAPMaxError_le_prim_divisors hqQ hx hQx
  have hsum_all := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum_all
  -- Swap `(q, d)` sum
  have hswap :
      ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ =
        ∑ d ∈ Finset.Icc 3 Q,
          (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have h1 : ∀ q ∈ Finset.Icc 1 Q,
        (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ =
        ∑ d ∈ Finset.Icc 3 Q,
          if d ∣ q then
            (q.totient : ℝ)⁻¹ *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
          else 0 := by
      intro q _
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hd_bound :
      ∑ d ∈ Finset.Icc 3 Q,
          (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
        12 * Real.log x *
          ∑ k ∈ Finset.Ico 2 Q,
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hle1 :
        ∑ d ∈ Finset.Icc 3 Q,
            (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
          ∑ d ∈ Finset.Icc 3 Q,
            (12 * Real.log x * (1 / (d.totient : ℝ))) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
      refine Finset.sum_le_sum fun d hd => ?_
      have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      have hdQ : d ≤ Q := (Finset.mem_Icc.mp hd).2
      have hdiv := Stage8BarbanDavenport.sum_inv_totient_dvd_le hd1 hdQ
      have hlog_le : Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ 2 * Real.log x := by
        have h1 : 2 * (Q : ℝ) / (d : ℝ) ≤ 2 * (Q : ℝ) :=
          div_le_self (by positivity) (by exact_mod_cast hd1)
        exact (Real.log_le_log (by positivity) h1).trans hlog2Q
      have hcoef : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ ≤
          12 * Real.log x * (1 / (d.totient : ℝ)) := by
        have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
        calc _ ≤ (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := hdiv
          _ ≤ (6 / (d.totient : ℝ)) * (2 * Real.log x) :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ = 12 * Real.log x * (1 / (d.totient : ℝ)) := by ring
      exact mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine hle1.trans_eq ?_
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢; omega
    · intro k₁ _ k₂ _ h; omega
    · intro d hd; simp only [Finset.mem_Icc] at hd
      exact ⟨d - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; ring
  have h1_le := mul_le_mul_of_nonneg_right hsum_inv (by positivity : 0 ≤ |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2)
  linarith

/-- Helper: for any `M > 0`, `∃ X ≥ 4, ∀ x ≥ X, (Real.log x) ^ M ≤ x ^ (1 / 8 : ℝ)`. -/
private lemma eventually_log_rpow_le_rpow_eighth (M : ℝ) (hM : 0 < M) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x → (Real.log x) ^ M ≤ x ^ (1 / 8 : ℝ) := by
  have hα : (0 : ℝ) < 1 / (8 * M) := by positivity
  have hev := ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlt : Real.log x / x ^ (1 / (8 * M)) < 1 := hX₁ x hx1
  have hle1 : Real.log x ≤ x ^ (1 / (8 * M)) :=
    ((div_lt_one (Real.rpow_pos_of_pos hx0 _)).mp hlt).le
  have hpow := Real.rpow_le_rpow hLx_nn hle1 hM.le
  rw [← Real.rpow_mul hx0.le] at hpow
  have hexp : 1 / (8 * M) * M = 1 / 8 := by field_simp [hM.ne']
  rwa [hexp] at hpow

/-- Helper: for any `c > 0` and `P > 0`, `∃ X ≥ 4, ∀ x ≥ X, (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1`. -/
private lemma eventually_log_rpow_mul_exp_neg_sqrt_le_one {c P : ℝ} (hc : 0 < c) (hP : 0 < P) :
    ∃ X : ℝ, 4 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      (Real.log x) ^ P * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos hc hP))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
  have hlt : Real.log (Real.log x) / Real.sqrt (Real.log x) < c / P := hX₁ x hx1
  have hmul : P * Real.log (Real.log x) < c * Real.sqrt (Real.log x) := by
    have h1 := (div_lt_iff₀ hsq_pos).mp hlt
    have h2 := mul_lt_mul_of_pos_left h1 hP
    have h3 : P * (c / P * Real.sqrt (Real.log x)) = c * Real.sqrt (Real.log x) := by
      field_simp [hP.ne']
    linarith
  rw [Real.rpow_def_of_pos hLx_pos, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith)

private lemma sum_biUnion_le_local {α β : Type*} [DecidableEq β] (s : Finset α)
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

open Classical in
/-- **UNCONDITIONAL BOMBIERI–VINOGRADOV THEOREM (`ϑ = 1/2`, `0` ASSUMPTIONS!)**:
for EVERY `A : ℝ`, there exist `B > 0` and `C > 0` such that for ALL `x ≥ 3`:
`∑_{q ≤ √x / (log x)^B} max_{(a, q) = 1} |ψ(x; q, a) - x / φ(q)| ≤ C * x / (log x)^A`. -/
theorem bombieri_vinogradov (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊,
          psiAPMaxError q x ≤ C * x / (Real.log x) ^ A := by
  set A' : ℝ := max A 1 with hA'_def
  have hA'1 : 1 ≤ A' := le_max_right A 1
  have hA_le_A' : A ≤ A' := le_max_left A 1
  set B : ℝ := 2 * A' + 20 with hB_def
  set B₁ : ℝ := A' + 10 with hB1_def
  set E : ℝ := 2 * A' + 16 with hE_def
  set K : ℝ := 4 * A' + 40 with hK_def
  set M_exp : ℝ := 10 * A' + 100 with hM_def
  have hB_pos : 0 < B := by dsimp only [B]; linarith
  have hB1_pos : 0 < B₁ := by dsimp only [B₁]; linarith
  have hE_pos : 0 < E := by dsimp only [E]; linarith
  have hK_pos : 0 < K := by dsimp only [K]; linarith
  -- Obtain unconditional zero-exception Siegel–Walfisz bounds
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_character_psi_uniform
  obtain ⟨C_sw, hC_sw, hsw_char⟩ := hsw_all B₁ hB1_pos
  obtain ⟨c_psi, hc_psi, hpsi_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_psi
  obtain ⟨C_psi, hC_psi, hpsi_ap⟩ := hpsi_all 1 one_pos
  -- Obtain asymptotic thresholds `X_0 ≥ exp 2`
  obtain ⟨X_pow, hX_pow4, hlog_pow⟩ := eventually_log_rpow_le_rpow_eighth M_exp (by dsimp only [M_exp]; linarith)
  obtain ⟨X_sw, hX_sw4, hlog_sw⟩ := eventually_log_rpow_mul_exp_neg_sqrt_le_one hc_sw (by dsimp only [B₁]; linarith : 0 < B₁ + A' + 5)
  obtain ⟨X_psi, hX_psi4, hlog_psi⟩ := eventually_log_rpow_mul_exp_neg_sqrt_le_one hc_psi (by linarith : 0 < A' + 5)
  set X₀ : ℝ := max (max (Real.exp 2) X_pow) (max X_sw X_psi) with hX₀_def
  have hX₀_ge4 : 4 ≤ X₀ := hX_pow4.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hX₀_ge3 : 3 ≤ X₀ := by linarith
  have hlogX₀_gt1 : 1 < Real.log X₀ := by
    have : Real.exp 1 < X₀ := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  -- Large-`x` constant and small-`x` constant
  set C_large : ℝ := 12 * C_psi + 12 * C_sw + 100000000 with hClarge_def
  have hClarge_pos : 0 < C_large := by positivity
  set C_small : ℝ := (X₀ * (X₀ * Real.log X₀ + X₀) + 1) * (Real.log X₀) ^ A' / 3 with hCsmall_def
  have hCsmall_pos : 0 < C_small := by
    have : 0 < (Real.log X₀) ^ A' := Real.rpow_pos_of_pos (by linarith) A'
    positivity
  set C : ℝ := max C_large C_small with hC_def
  refine ⟨B, C, hB_pos, lt_of_lt_of_le hClarge_pos (le_max_left _ _), fun x hx3 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  -- Since `log x > 1`, `x / (log x)^A' ≤ x / (log x)^A`
  have hA'_to_A : C * x / (Real.log x) ^ A' ≤ C * x / (Real.log x) ^ A :=
    div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLx_pos A)
      (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hA_le_A')
  refine le_trans ?_ hA'_to_A
  set Q : ℕ := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊ with hQ_def
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    have : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    positivity
  · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
    by_cases hx_big : X₀ ≤ x
    · -- Case 1: Large `x ≥ X₀`
      have hx4 : 4 ≤ x := hX₀_ge4.trans hx_big
      have hLx_ge2 : 2 ≤ Real.log x := by
        have he2 : Real.exp 2 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx_big
        have h := Real.log_le_log (Real.exp_pos 2) he2
        rwa [Real.log_exp] at h
      have hpow_bd : (Real.log x) ^ M_exp ≤ x ^ (1 / 8 : ℝ) :=
        hlog_pow x (((le_max_right _ _).trans (le_max_left _ _)).trans hx_big)
      have hsw_decay : (Real.log x) ^ (B₁ + A' + 5) * Real.exp (-c_sw * Real.sqrt (Real.log x)) ≤ 1 :=
        hlog_sw x (((le_max_left _ _).trans (le_max_right _ _)).trans hx_big)
      have hpsi_decay : (Real.log x) ^ (A' + 5) * Real.exp (-c_psi * Real.sqrt (Real.log x)) ≤ 1 :=
        hlog_psi x (((le_max_right _ _).trans (le_max_right _ _)).trans hx_big)
      have hL_le_x8 : ∀ p : ℝ, 0 ≤ p → p ≤ M_exp → (Real.log x) ^ p ≤ x ^ (1 / 8 : ℝ) := fun p _ hpM =>
        (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le hpM).trans hpow_bd
      have hQR_le : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B :=
        Nat.floor_le (by positivity)
      have hQ_le_x : (Q : ℝ) ≤ x := by
        calc (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B := hQR_le
          _ ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le)
          _ ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      -- Start from primitive-character reduction
      have hred := sum_psiAPMaxError_le_prim_sum hQ1 hx3 hQ_le_x
      -- Bound 1: Principal term `12 * log x * (|ψ(x) - x| + 2 * (log x)^2)`
      have hpsi_err : |RHDirect.chebyshevPsi x - x| ≤ C_psi * x * Real.exp (-c_psi * Real.sqrt (Real.log x)) := by
        have h1 := hpsi_ap x hx4 1 (by simp; linarith) 1 (Nat.coprime_one_left 1)
        have hEq : Stage2DirichletAP.chebyshevPsiAP 1 1 x = RHDirect.chebyshevPsi x := by
          unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [if_pos (by show n % 1 = 1 % 1; exact Nat.mod_one n)]
        rw [hEq, Nat.totient_one, Nat.cast_one, div_one] at h1
        exact h1
      have hterm_princ :
          12 * Real.log x * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) ≤
            (12 * C_psi + 24) * x / (Real.log x) ^ A' := by
        have h1 : Real.log x * (C_psi * x * Real.exp (-c_psi * Real.sqrt (Real.log x))) ≤
            C_psi * x / (Real.log x) ^ A' := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
          have hpow1 : (Real.log x) ^ (1 : ℝ) * (Real.log x) ^ A' ≤ (Real.log x) ^ (A' + 5) := by
            rw [← Real.rpow_add hLx_pos]
            exact Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
          rw [Real.rpow_one] at hpow1
          calc Real.log x * (C_psi * x * Real.exp (-c_psi * Real.sqrt (Real.log x))) * (Real.log x) ^ A'
              = C_psi * x * ((Real.log x * (Real.log x) ^ A') * Real.exp (-c_psi * Real.sqrt (Real.log x))) := by ring
            _ ≤ C_psi * x * ((Real.log x) ^ (A' + 5) * Real.exp (-c_psi * Real.sqrt (Real.log x))) := by gcongr
            _ ≤ C_psi * x * 1 := mul_le_mul_of_nonneg_left hpsi_decay (by positivity)
            _ = C_psi * x := mul_one _
        have h2 : (Real.log x) ^ 3 ≤ x / (Real.log x) ^ A' := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
          have h3A : (Real.log x) ^ 3 * (Real.log x) ^ A' = (Real.log x) ^ (A' + 3) := by
            rw [← Real.rpow_natCast (Real.log x) 3, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
          rw [h3A]
          calc (Real.log x) ^ (A' + 3) ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 (A' + 3) (by linarith) (by dsimp only [M_exp]; linarith)
            _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = x := Real.rpow_one x
        have h3 : 12 * Real.log x * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) ≤
            12 * (Real.log x * (C_psi * x * Real.exp (-c_psi * Real.sqrt (Real.log x)))) +
            24 * (Real.log x) ^ 3 := by
          have := mul_le_mul_of_nonneg_left hpsi_err (show 0 ≤ 12 * Real.log x by positivity)
          linarith
        have hEq : (12 * C_psi + 24) * x / (Real.log x) ^ A' =
            12 * (C_psi * x / (Real.log x) ^ A') + 24 * (x / (Real.log x) ^ A') := by ring
        linarith
      -- Bound 2: `Q * (log x)^2 ≤ x / (log x)^A'`
      have hterm_Qlog : (Q : ℝ) * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ A' := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
        have h1 : (Q : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
          exact hQR_le.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le))
        have h2 : (Real.log x) ^ 2 * (Real.log x) ^ A' ≤ x ^ (1 / 8 : ℝ) := by
          have hEq : (Real.log x) ^ 2 * (Real.log x) ^ A' = (Real.log x) ^ (A' + 2) := by
            rw [← Real.rpow_natCast (Real.log x) 2, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
          rw [hEq]
          exact hL_le_x8 (A' + 2) (by linarith) (by dsimp only [M_exp]; linarith)
        calc (Q : ℝ) * (Real.log x) ^ 2 * (Real.log x) ^ A'
            = (Q : ℝ) * ((Real.log x) ^ 2 * (Real.log x) ^ A') := by ring
          _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = x ^ (5 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
          _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = x := Real.rpow_one x
      -- Bound 3: Split primitive characters `k ∈ Ico 2 Q` at `Q₁ = ⌊(log x)^B₁⌋₊`
      set Q₁ : ℕ := ⌊(Real.log x) ^ B₁⌋₊ with hQ1_def
      have hQ1_ge2 : 2 ≤ Q₁ := by
        have h2B1 : (2 : ℝ) ≤ (Real.log x) ^ B₁ := by
          calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
            _ ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hLx_ge2 (by norm_num)
            _ ≤ (Real.log x) ^ B₁ := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B₁]; linarith)
        exact Nat.le_floor h2B1
      have hQ1_le_R : (Q₁ : ℝ) ≤ (Real.log x) ^ B₁ := Nat.floor_le (by positivity)
      have hQ1_ge_half : (Real.log x) ^ B₁ / 2 ≤ (Q₁ : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((Real.log x) ^ B₁)
        have h2 : (2 : ℝ) ≤ (Q₁ : ℝ) := by exact_mod_cast hQ1_ge2
        linarith
      -- Split `Ico 2 Q` into `Ico 2 (min Q₁ Q)` and `Ico Q₁ Q`
      have hsplit_prim :
          ∑ k ∈ Finset.Ico 2 Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
            (∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖) +
            (∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖) := by
        by_cases hQQ1 : Q ≤ Q₁
        · have hmin : min Q₁ Q = Q := Nat.min_eq_right hQQ1
          have hempty : Finset.Ico Q₁ Q = ∅ := Finset.Ico_eq_empty (by omega)
          rw [hmin, hempty, Finset.sum_empty, add_zero]
        · push Not at hQQ1
          have hmin : min Q₁ Q = Q₁ := Nat.min_eq_left hQQ1.le
          rw [hmin]
          have hunion : Finset.Ico 2 Q = Finset.Ico 2 Q₁ ∪ Finset.Ico Q₁ Q := by
            ext k; simp only [Finset.mem_Ico, Finset.mem_union]; omega
          have hdisj : Disjoint (Finset.Ico 2 Q₁) (Finset.Ico Q₁ Q) := by
            rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
          rw [hunion, Finset.sum_union hdisj]
      -- Bound 3a: Small conductors `k ∈ Ico 2 (min Q₁ Q)` via Siegel–Walfisz
      have hsmall_cond :
          12 * Real.log x *
            ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
            12 * C_sw * x / (Real.log x) ^ A' := by
        have hper_k : ∀ k ∈ Finset.Ico 2 (min Q₁ Q),
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
              C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := by
          intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
          have hkQ1 : k + 1 ≤ Q₁ := by have := (Finset.mem_Ico.mp hk).2; omega
          have hmod_le : ((k + 1 : ℕ) : ℝ) ≤ (Real.log x) ^ B₁ :=
            (by exact_mod_cast hkQ1 : ((k + 1 : ℕ) : ℝ) ≤ (Q₁ : ℝ)).trans hQ1_le_R
          have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
            Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
          have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
            rw [← Nat.card_eq_fintype_card]
            exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
          have hcard :
              ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) ≤
                (Nat.totient (k + 1) : ℝ) := by
            have hnat : (Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card ≤
                (k + 1).totient := by
              calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).card := Finset.card_filter_le _ _
                _ = (k + 1).totient := by rw [Finset.card_univ, htot]
            exact_mod_cast hnat
          calc (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
              ≤ (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ _ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
                refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ψ hψ => ?_) (by positivity)
                have hprim : ψ.IsPrimitive := (Finset.mem_filter.mp hψ).2
                have hne1 : ψ ≠ 1 := by
                  intro h1
                  have hc : ψ.conductor = k + 1 := hprim
                  rw [h1, DirichletCharacter.conductor_one] at hc
                  omega
                exact hsw_char x hx4 (k + 1) hmod_le ψ hne1
            _ = (((Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive)).card : ℝ) /
                  (Nat.totient (k + 1) : ℝ)) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
            _ ≤ 1 * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) :=
                mul_le_mul_of_nonneg_right ((div_le_one hphi_pos).mpr hcard) (by positivity)
            _ = C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)) := one_mul _
        have hsum_k :
            ∑ k ∈ Finset.Ico 2 (min Q₁ Q),
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
              (Q₁ : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
          calc _ ≤ ∑ _k ∈ Finset.Ico 2 (min Q₁ Q), (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) :=
                  Finset.sum_le_sum hper_k
            _ = ((Finset.Ico 2 (min Q₁ Q)).card : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Q₁ : ℝ) * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [Nat.card_Ico]; exact_mod_cast (by omega : min Q₁ Q - 2 ≤ Q₁)
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
        have hpow_le : Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A' ≤ (Real.log x) ^ (B₁ + A' + 5) := by
          have hEq : (Real.log x) ^ (1 + B₁ + A') = Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A' := by
            rw [Real.rpow_add hLx_pos, Real.rpow_add hLx_pos, Real.rpow_one]
          rw [← hEq]
          exact Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by linarith)
        calc 12 * Real.log x *
              (∑ k ∈ Finset.Ico 2 (min Q₁ Q),
                (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖) * (Real.log x) ^ A'
            ≤ 12 * Real.log x * ((Real.log x) ^ B₁ * (C_sw * x * Real.exp (-c_sw * Real.sqrt (Real.log x)))) *
                (Real.log x) ^ A' := by
              have h1 := hsum_k.trans (mul_le_mul_of_nonneg_right hQ1_le_R (by positivity))
              have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 12 * Real.log x by positivity)
              exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLx_pos.le A')
          _ = 12 * C_sw * x * ((Real.log x * (Real.log x) ^ B₁ * (Real.log x) ^ A') *
                Real.exp (-c_sw * Real.sqrt (Real.log x))) := by ring
          _ ≤ 12 * C_sw * x * ((Real.log x) ^ (B₁ + A' + 5) * Real.exp (-c_sw * Real.sqrt (Real.log x))) := by
              gcongr
          _ ≤ 12 * C_sw * x * 1 := mul_le_mul_of_nonneg_left hsw_decay (by positivity)
          _ = 12 * C_sw * x := mul_one _
      -- Bound 3b: Large conductors `k ∈ Ico Q₁ Q` via Dyadic Vaughan + Large Sieve!
      have hlarge_cond :
          12 * Real.log x *
            ∑ k ∈ Finset.Ico Q₁ Q,
              (1 / (Nat.totient (k + 1) : ℝ)) *
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
            99999000 * x / (Real.log x) ^ A' := by
        by_cases hQQ1 : Q ≤ Q₁
        · have hempty : Finset.Ico Q₁ Q = ∅ := Finset.Ico_eq_empty (by omega)
          rw [hempty, Finset.sum_empty, mul_zero]; positivity
        · push Not at hQQ1
          set Δ : ℝ := (Real.log x) ^ (-E) with hΔ_def
          have hΔ0 : 0 < Δ := Real.rpow_pos_of_pos hLx_pos (-E)
          have hΔ1 : Δ < 1 := by
            rw [hΔ_def, Real.rpow_neg hLx_pos.le]
            exact inv_lt_one_of_one_lt₀ (by
              calc (1 : ℝ) < Real.log x := hLx_gt1
                _ = (Real.log x) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (Real.log x) ^ E := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E]; linarith))
          set U : ℕ := ⌊(Real.log x) ^ K⌋₊ with hU_def
          have hU_ge2 : 2 ≤ U := by
            have h2K : (2 : ℝ) ≤ (Real.log x) ^ K := by
              calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
                _ ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hLx_ge2 (by norm_num)
                _ ≤ (Real.log x) ^ K := Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [K]; linarith)
            exact Nat.le_floor h2K
          have hU_le_R : (U : ℝ) ≤ (Real.log x) ^ K := Nat.floor_le (by positivity)
          have hU_ge_half : (Real.log x) ^ K / 2 ≤ (U : ℝ) := by
            have hlt := Nat.lt_floor_add_one ((Real.log x) ^ K)
            have h2 : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU_ge2
            linarith
          have hU_le_x : (U : ℝ) ≤ x := by
            calc (U : ℝ) ≤ (Real.log x) ^ K := hU_le_R
              _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 K hK_pos.le (by dsimp only [K, M_exp]; linarith)
              _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
              _ = x := Real.rpow_one x
          -- Cover `Ico Q₁ Q` by `J = Nat.log 2 (Q / Q₁) + 1` dyadic blocks `Ico (Q₁ * 2^j) (2 * (Q₁ * 2^j))`
          set J : ℕ := Nat.log 2 (Q / Q₁) + 1 with hJ_def
          have hcover : Finset.Ico Q₁ Q ⊆
              (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))) := by
            intro k hk
            simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range] at hk ⊢
            refine ⟨Nat.log 2 (k / Q₁), ?_, ?_, ?_⟩
            · have hdiv_le : k / Q₁ ≤ Q / Q₁ := Nat.div_le_div_right hk.2.le
              have hlog_le : Nat.log 2 (k / Q₁) ≤ Nat.log 2 (Q / Q₁) := Nat.log_mono_right hdiv_le
              omega
            · have hk_div : 1 ≤ k / Q₁ := Nat.div_pos hk.1 (by omega)
              have hpow : 2 ^ Nat.log 2 (k / Q₁) ≤ k / Q₁ := Nat.pow_log_le_self 2 (by omega)
              calc Q₁ * 2 ^ Nat.log 2 (k / Q₁) ≤ Q₁ * (k / Q₁) := Nat.mul_le_mul_left Q₁ hpow
                _ ≤ k := Nat.mul_div_le k Q₁
            · have hlt : k / Q₁ < 2 ^ (Nat.log 2 (k / Q₁) + 1) :=
                Nat.lt_pow_succ_log_self (by omega) (k / Q₁)
              have hdiv := Nat.div_add_mod k Q₁
              have hmod : k % Q₁ < Q₁ := Nat.mod_lt k (by omega)
              have hpow : 2 ^ (Nat.log 2 (k / Q₁) + 1) = 2 * 2 ^ Nat.log 2 (k / Q₁) := by
                rw [pow_succ, mul_comm]
              have h1 : k < Q₁ * (k / Q₁ + 1) := by nlinarith
              have h2 : k / Q₁ + 1 ≤ 2 * 2 ^ Nat.log 2 (k / Q₁) := by omega
              calc k < Q₁ * (k / Q₁ + 1) := h1
                _ ≤ Q₁ * (2 * 2 ^ Nat.log 2 (k / Q₁)) := Nat.mul_le_mul_left Q₁ h2
                _ = 2 * (Q₁ * 2 ^ Nat.log 2 (k / Q₁)) := by ring
          have hbiUnion_le :
              ∑ k ∈ Finset.Ico Q₁ Q,
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
                ∑ j ∈ Finset.range J,
                  ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
                    (1 / (Nat.totient (k + 1) : ℝ)) *
                      ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                        ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
            calc _ ≤ ∑ k ∈ (Finset.range J).biUnion (fun j => Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j))),
                      (1 / (Nat.totient (k + 1) : ℝ)) *
                        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                          ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ :=
                    Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ =>
                      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
              _ ≤ _ := sum_biUnion_le_local _ _ _ fun _ =>
                    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          -- Bound each dyadic block `j < J` (with `D = Q₁ * 2^j ∈ [Q₁, Q]`) by `50000 * x / (log x)^(A' + 2)`!
          have hper_j : ∀ j ∈ Finset.range J,
              ∑ k ∈ Finset.Ico (Q₁ * 2 ^ j) (2 * (Q₁ * 2 ^ j)),
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
                60000 * x / (Real.log x) ^ (A' + 2) := by
            intro j hj
            set D : ℕ := Q₁ * 2 ^ j
            have hD1 : 1 ≤ D := Nat.mul_pos (by omega) (by positivity)
            have hD_ge_Q1 : Q₁ ≤ D := Nat.le_mul_of_pos_right Q₁ (by positivity)
            have hD_le_Q : D ≤ Q := by
              have hj_le : j ≤ Nat.log 2 (Q / Q₁) := by have := Finset.mem_range.mp hj; omega
              have hpow : 2 ^ j ≤ Q / Q₁ :=
                (Nat.pow_le_pow_right (by omega) hj_le).trans (Nat.pow_log_le_self 2 (by
                  have : 1 ≤ Q / Q₁ := Nat.div_pos hQQ1.le (by omega); omega))
              calc D = Q₁ * 2 ^ j := rfl
                _ ≤ Q₁ * (Q / Q₁) := Nat.mul_le_mul_left Q₁ hpow
                _ ≤ Q := Nat.mul_div_le Q Q₁
            have hD_le_QR : (D : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B :=
              (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQR_le
            have hD_le_x : (D : ℝ) ≤ x := (by exact_mod_cast hD_le_Q : (D : ℝ) ≤ (Q : ℝ)).trans hQ_le_x
            have hD_le_sqx : (D : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
              rw [← Real.sqrt_eq_rpow]
              exact hD_le_QR.trans (div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le))
            have hdy := dyadic_prim_chebyshevPsiChar_bound hD1 (by omega : 1 ≤ U) (by omega : 1 ≤ U)
              hx3 hD_le_x hU_le_x hΔ0 hΔ1
            -- Bound each of the 9 terms inside `hdy` by `2 * x / (log x)^(A' + 6)`
            have hsqrtΔ : Real.sqrt Δ = (Real.log x) ^ (-(E / 2)) := by
              rw [hΔ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hLx_pos.le]; congr 1; ring
            have hsqrtU_ge : (Real.log x) ^ (K / 2) / 2 ≤ Real.sqrt (U : ℝ) := by
              have h1 : Real.sqrt ((Real.log x) ^ K / 2) ≤ Real.sqrt (U : ℝ) := Real.sqrt_le_sqrt hU_ge_half
              have h2 : (Real.log x) ^ (K / 2) / 2 ≤ Real.sqrt ((Real.log x) ^ K / 2) := by
                rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hLx_pos.le,
                  show K * (1 / 2 : ℝ) = K / 2 by ring]
                exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by norm_num))
                  (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
              exact h2.trans h1
            have ht1 : (D : ℝ) * (U : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _)]
              have h1 : (U : ℝ) * (Real.log x) ^ (A' + 6) ≤ x ^ (1 / 8 : ℝ) := by
                have hEq : (Real.log x) ^ K * (Real.log x) ^ (A' + 6) = (Real.log x) ^ (K + A' + 6) := by
                  rw [← Real.rpow_add hLx_pos]; congr 1; ring
                calc (U : ℝ) * (Real.log x) ^ (A' + 6)
                    ≤ (Real.log x) ^ K * (Real.log x) ^ (A' + 6) :=
                      mul_le_mul_of_nonneg_right hU_le_R (by positivity)
                  _ = (Real.log x) ^ (K + A' + 6) := hEq
                  _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 _ (by dsimp only [K]; linarith) (by dsimp only [K, M_exp]; linarith)
              calc (D : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)
                  = (D : ℝ) * ((U : ℝ) * (Real.log x) ^ (A' + 6)) := by ring
                _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul hD_le_sqx h1 (by positivity) (by positivity)
                _ = x ^ (5 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
                _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
                _ = x := Real.rpow_one x
                _ ≤ 2 * x := by linarith
            have ht2 : (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _)]
              have hD32 : (D : ℝ) * Real.sqrt (D : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
                have hsqD : Real.sqrt (D : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
                  rw [Real.sqrt_eq_rpow]
                  calc ((D : ℝ)) ^ (1 / 2 : ℝ) ≤ (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
                        Real.rpow_le_rpow (Nat.cast_nonneg _) hD_le_sqx (by norm_num)
                    _ = x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hx0.le]; norm_num
                calc (D : ℝ) * Real.sqrt (D : ℝ) ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) :=
                      mul_le_mul hD_le_sqx hsqD (Real.sqrt_nonneg _) (by positivity)
                  _ = x ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
              have hU2 : (U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6) ≤ x ^ (1 / 8 : ℝ) := by
                have hEq : (Real.log x) ^ K * (Real.log x) ^ K * (Real.log x) ^ (A' + 6) =
                    (Real.log x) ^ (2 * K + A' + 6) := by
                  rw [← Real.rpow_add hLx_pos, ← Real.rpow_add hLx_pos]; congr 1; ring
                calc (U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)
                    ≤ (Real.log x) ^ K * (Real.log x) ^ K * (Real.log x) ^ (A' + 6) := by gcongr
                  _ = (Real.log x) ^ (2 * K + A' + 6) := hEq
                  _ ≤ x ^ (1 / 8 : ℝ) := hL_le_x8 _ (by dsimp only [K]; linarith) (by dsimp only [K, M_exp]; linarith)
              calc (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) * (Real.log x) ^ (A' + 6)
                  = ((U : ℝ) * (U : ℝ) * (Real.log x) ^ (A' + 6)) * ((D : ℝ) * Real.sqrt (D : ℝ)) := by ring
                _ ≤ x ^ (1 / 8 : ℝ) * x ^ (3 / 4 : ℝ) := mul_le_mul hU2 hD32 (by positivity) (by positivity)
                _ = x ^ (7 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
                _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
                _ = x := Real.rpow_one x
                _ ≤ 2 * x := by linarith
            have ht3 : x / (D : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              have hD_lo : (Real.log x) ^ (A' + 6) / 2 ≤ (D : ℝ) := by
                calc (Real.log x) ^ (A' + 6) / 2
                    ≤ (Real.log x) ^ B₁ / 2 := div_le_div_of_nonneg_right
                      (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B₁]; linarith)) (by norm_num)
                  _ ≤ (Q₁ : ℝ) := hQ1_ge_half
                  _ ≤ (D : ℝ) := by exact_mod_cast hD_ge_Q1
              calc x / (D : ℝ) ≤ x / ((Real.log x) ^ (A' + 6) / 2) :=
                    div_le_div_of_nonneg_left hx0.le (by positivity) hD_lo
                _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
            have ht4 : x / Real.sqrt (U : ℝ) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              have hU_lo : (Real.log x) ^ (A' + 6) / 2 ≤ Real.sqrt (U : ℝ) := by
                calc (Real.log x) ^ (A' + 6) / 2
                    ≤ (Real.log x) ^ (K / 2) / 2 := div_le_div_of_nonneg_right
                      (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [K]; linarith)) (by norm_num)
                  _ ≤ Real.sqrt (U : ℝ) := hsqrtU_ge
              calc x / Real.sqrt (U : ℝ) ≤ x / ((Real.log x) ^ (A' + 6) / 2) :=
                    div_le_div_of_nonneg_left hx0.le (by positivity) hU_lo
                _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
            have ht5 : x / Real.sqrt (Δ * (U : ℝ)) ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [Real.sqrt_mul hΔ0.le, hsqrtΔ]
              have hden : (Real.log x) ^ (A' + 6) / 2 ≤ (Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ) := by
                calc (Real.log x) ^ (A' + 6) / 2
                    ≤ (Real.log x) ^ (-(E / 2) + K / 2) / 2 := div_le_div_of_nonneg_right
                      (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E, K]; linarith)) (by norm_num)
                  _ = (Real.log x) ^ (-(E / 2)) * ((Real.log x) ^ (K / 2) / 2) := by
                      rw [Real.rpow_add hLx_pos]; ring
                  _ ≤ (Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ) :=
                      mul_le_mul_of_nonneg_left hsqrtU_ge (by positivity)
              calc x / ((Real.log x) ^ (-(E / 2)) * Real.sqrt (U : ℝ))
                  ≤ x / ((Real.log x) ^ (A' + 6) / 2) := div_le_div_of_nonneg_left hx0.le (by positivity) hden
                _ = 2 * x / (Real.log x) ^ (A' + 6) := by ring
            have ht6 : (D : ℝ) * Real.sqrt x / Real.sqrt Δ ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [hsqrtΔ, Real.rpow_neg hLx_pos.le, div_inv_eq_mul]
              calc (D : ℝ) * Real.sqrt x * (Real.log x) ^ (E / 2)
                  ≤ (Real.sqrt x / (Real.log x) ^ B) * Real.sqrt x * (Real.log x) ^ (E / 2) := by gcongr
                _ = (Real.sqrt x * Real.sqrt x) * ((Real.log x) ^ (E / 2) / (Real.log x) ^ B) := by ring
                _ = x / (Real.log x) ^ (B - E / 2) := by
                    rw [Real.mul_self_sqrt hx0.le, ← Real.rpow_sub hLx_pos,
                      show E / 2 - B = -(B - E / 2) by ring, Real.rpow_neg hLx_pos.le, ← div_eq_mul_inv]
                _ ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                    (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B, E]; linarith))
                _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                    div_le_div_of_nonneg_right (by linarith) (by positivity)
            have ht7 : Real.sqrt Δ * x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [hsqrtΔ, Real.rpow_neg hLx_pos.le, inv_mul_eq_div]
              calc x / (Real.log x) ^ (E / 2)
                  ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                    (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [E]; linarith))
                _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                    div_le_div_of_nonneg_right (by linarith) (by positivity)
            have ht8 : Real.sqrt x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos _), Real.sqrt_eq_rpow]
              calc x ^ (1 / 2 : ℝ) * (Real.log x) ^ (A' + 6)
                  ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left
                    (hL_le_x8 _ (by linarith) (by dsimp only [M_exp]; linarith)) (by positivity)
                _ = x ^ (5 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
                _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
                _ = x := Real.rpow_one x
                _ ≤ 2 * x := by linarith
            have ht9 : (D : ℝ) * Real.sqrt x ≤ 2 * x / (Real.log x) ^ (A' + 6) := by
              calc (D : ℝ) * Real.sqrt x
                  ≤ (Real.sqrt x / (Real.log x) ^ B) * Real.sqrt x := by gcongr
                _ = (Real.sqrt x * Real.sqrt x) / (Real.log x) ^ B := by ring
                _ = x / (Real.log x) ^ B := by rw [Real.mul_self_sqrt hx0.le]
                _ ≤ x / (Real.log x) ^ (A' + 6) := div_le_div_of_nonneg_left hx0.le (by positivity)
                    (Real.rpow_le_rpow_of_exponent_le hLx_gt1.le (by dsimp only [B]; linarith))
                _ ≤ 2 * x / (Real.log x) ^ (A' + 6) :=
                    div_le_div_of_nonneg_right (by linarith) (by positivity)
            have h9 :
                ((D : ℝ) * (U : ℝ) + (U : ℝ) * (U : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
                  x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (U : ℝ)) +
                  (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
                  (D : ℝ) * Real.sqrt x) ≤ 18 * x / (Real.log x) ^ (A' + 6) := by
              have hEq : 18 * x / (Real.log x) ^ (A' + 6) = 9 * (2 * x / (Real.log x) ^ (A' + 6)) := by ring
              linarith
            have hlog4 : (1 + Real.log x) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
              have h1 : 1 + Real.log x ≤ 2 * Real.log x := by linarith
              calc (1 + Real.log x) ^ 4 ≤ (2 * Real.log x) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
                _ = 16 * (Real.log x) ^ 4 := by ring
            have hpow_cancel : (x / (Real.log x) ^ (A' + 6)) * (Real.log x) ^ 4 =
                x / (Real.log x) ^ (A' + 2) := by
              have hsplit : (Real.log x) ^ (A' + 6) = (Real.log x) ^ (A' + 2) * (Real.log x) ^ (4 : ℕ) := by
                rw [← Real.rpow_natCast (Real.log x) 4, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
              rw [hsplit]
              have hne1 : (Real.log x) ^ (A' + 2) ≠ 0 := (Real.rpow_pos_of_pos hLx_pos _).ne'
              have hne2 : (Real.log x) ^ (4 : ℕ) ≠ 0 := pow_ne_zero 4 hLx_pos.ne'
              field_simp [hne1, hne2]
            calc _ ≤ 180 * (18 * x / (Real.log x) ^ (A' + 6)) * (16 * (Real.log x) ^ 4) := by
                    refine hdy.trans (mul_le_mul (mul_le_mul_of_nonneg_left h9 (by norm_num)) hlog4
                      (by positivity) (by positivity))
              _ = 51840 * ((x / (Real.log x) ^ (A' + 6)) * (Real.log x) ^ 4) := by ring
              _ = 51840 * (x / (Real.log x) ^ (A' + 2)) := by rw [hpow_cancel]
              _ ≤ 60000 * x / (Real.log x) ^ (A' + 2) := by
                    have : 0 ≤ x / (Real.log x) ^ (A' + 2) := by positivity
                    have hEq : 60000 * x / (Real.log x) ^ (A' + 2) = 60000 * (x / (Real.log x) ^ (A' + 2)) := by ring
                    linarith
          -- Sum over `j ∈ Finset.range J` using `J ≤ 4 * Real.log x`
          have hJ_le : (J : ℝ) ≤ 4 * Real.log x := by
            have hdiv_pos : 1 ≤ Q / Q₁ := Nat.div_pos hQQ1.le (by omega)
            have hpow : 2 ^ Nat.log 2 (Q / Q₁) ≤ Q / Q₁ := Nat.pow_log_le_self 2 (by omega)
            have hpowR : (2 : ℝ) ^ Nat.log 2 (Q / Q₁) ≤ x := by
              have h1 : 2 ^ Nat.log 2 (Q / Q₁) ≤ Q := hpow.trans (Nat.div_le_self Q Q₁)
              exact (by exact_mod_cast h1 : (2 : ℝ) ^ Nat.log 2 (Q / Q₁) ≤ (Q : ℝ)).trans hQ_le_x
            have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 (Q / Q₁)) hpowR
            rw [Real.log_pow] at hlog
            have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
            have hnat : (Nat.log 2 (Q / Q₁) : ℝ) ≤ 2 * Real.log x := by nlinarith
            dsimp only [J]; push_cast; linarith
          have hlog_cancel : (Real.log x) ^ 2 * (x / (Real.log x) ^ (A' + 2)) = x / (Real.log x) ^ A' := by
            have hsplit : (Real.log x) ^ (A' + 2) = (Real.log x) ^ A' * (Real.log x) ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast (Real.log x) 2, ← Real.rpow_add hLx_pos]; congr 1
            rw [hsplit]
            have hne1 : (Real.log x) ^ A' ≠ 0 := (Real.rpow_pos_of_pos hLx_pos _).ne'
            have hne2 : (Real.log x) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hLx_pos.ne'
            field_simp [hne1, hne2]
          calc 12 * Real.log x *
                ∑ k ∈ Finset.Ico Q₁ Q,
                  (1 / (Nat.totient (k + 1) : ℝ)) *
                    ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                      ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
              ≤ 12 * Real.log x * ((J : ℝ) * (60000 * x / (Real.log x) ^ (A' + 2))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                calc _ ≤ ∑ _j ∈ Finset.range J, (60000 * x / (Real.log x) ^ (A' + 2)) :=
                        hbiUnion_le.trans (Finset.sum_le_sum hper_j)
                  _ = (J : ℝ) * (60000 * x / (Real.log x) ^ (A' + 2)) := by
                        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ 12 * Real.log x * ((4 * Real.log x) * (60000 * x / (Real.log x) ^ (A' + 2))) := by
                gcongr
            _ = 2880000 * ((Real.log x) ^ 2 * (x / (Real.log x) ^ (A' + 2))) := by ring
            _ = 2880000 * (x / (Real.log x) ^ A') := by rw [hlog_cancel]
            _ ≤ 99999000 * x / (Real.log x) ^ A' := by
                have : 0 ≤ x / (Real.log x) ^ A' := by positivity
                have hEq : 99999000 * x / (Real.log x) ^ A' = 99999000 * (x / (Real.log x) ^ A') := by ring
                linarith
      -- Assemble all 3 bounds for `x ≥ X₀`!
      have htot :
          ∑ q ∈ Finset.Icc 1 Q, psiAPMaxError q x ≤ C_large * x / (Real.log x) ^ A' := by
        have hprim_comb :
            12 * Real.log x *
              ∑ k ∈ Finset.Ico 2 Q,
                (1 / (Nat.totient (k + 1) : ℝ)) *
                  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                    ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
              (12 * C_sw + 99999000) * x / (Real.log x) ^ A' := by
          have hmul := mul_le_mul_of_nonneg_left hsplit_prim (show 0 ≤ 12 * Real.log x by positivity)
          rw [mul_add] at hmul
          have hEq : (12 * C_sw + 99999000) * x / (Real.log x) ^ A' =
              12 * C_sw * x / (Real.log x) ^ A' + 99999000 * x / (Real.log x) ^ A' := by ring
          linarith
        have hC_eq : C_large * x / (Real.log x) ^ A' =
            (12 * C_psi + 24) * x / (Real.log x) ^ A' + x / (Real.log x) ^ A' +
            (12 * C_sw + 99999000) * x / (Real.log x) ^ A' +
            975 * (x / (Real.log x) ^ A') := by
          dsimp only [C_large]; ring
        have hnn : 0 ≤ 975 * (x / (Real.log x) ^ A') := by positivity
        linarith
      exact htot.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le) (by positivity))
    · -- Case 2: Small `3 ≤ x < X₀` — trivial uniform bound
      push Not at hx_big
      have hQR_le : (Q : ℝ) ≤ X₀ := by
        calc (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B := Nat.floor_le (by positivity)
          _ ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hLx_gt1.le hB_pos.le)
          _ ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
          _ ≤ X₀ := hx_big.le
      have hpsi_le : RHDirect.chebyshevPsi x ≤ x * Real.log x := by
        unfold RHDirect.chebyshevPsi
        calc ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n
            = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
              have h0 : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
                ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
              rw [h0, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
          _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
              have hnx : (n : ℝ) ≤ x :=
                (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx0.le)
              exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hn1) hnx)
          _ = (⌊x⌋₊ : ℝ) * Real.log x := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le) hLx_pos.le
      have hper_small : ∀ q ∈ Finset.Icc 1 Q, psiAPMaxError q x ≤ X₀ * Real.log X₀ + X₀ := by
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        refine psiAPMaxError_le_of_forall (by positivity) fun a _ => ?_
        have h1 : 0 ≤ Stage2DirichletAP.chebyshevPsiAP q a x := Stage2DirichletAP.chebyshevPsiAP_nonneg q a x
        have h2 : Stage2DirichletAP.chebyshevPsiAP q a x ≤ RHDirect.chebyshevPsi x := by
          unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
          refine Finset.sum_le_sum fun n _ => by split_ifs <;> [exact le_rfl; exact ArithmeticFunction.vonMangoldt_nonneg]
        have h3 : 0 ≤ x / (q.totient : ℝ) := by positivity
        have h4 : x / (q.totient : ℝ) ≤ x := div_le_self hx0.le (by exact_mod_cast Nat.totient_pos.mpr hq1)
        have h5 : x * Real.log x ≤ X₀ * Real.log X₀ :=
          mul_le_mul hx_big.le (Real.log_le_log hx0 hx_big.le) hLx_pos.le (by linarith)
        rw [abs_le]; constructor <;> linarith
      have hsum_small : ∑ q ∈ Finset.Icc 1 Q, psiAPMaxError q x ≤ X₀ * (X₀ * Real.log X₀ + X₀) := by
        calc ∑ q ∈ Finset.Icc 1 Q, psiAPMaxError q x
            ≤ ∑ _q ∈ Finset.Icc 1 Q, (X₀ * Real.log X₀ + X₀) := Finset.sum_le_sum hper_small
          _ = (Q : ℝ) * (X₀ * Real.log X₀ + X₀) := by
                rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          _ ≤ X₀ * (X₀ * Real.log X₀ + X₀) := mul_le_mul_of_nonneg_right hQR_le (by positivity)
      have hlog_le : (Real.log x) ^ A' ≤ (Real.log X₀) ^ A' :=
        Real.rpow_le_rpow hLx_pos.le (Real.log_le_log hx0 hx_big.le) (by linarith)
      have hlow : X₀ * (X₀ * Real.log X₀ + X₀) ≤ C_small * x / (Real.log x) ^ A' := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A')]
        have hEq : C_small * 3 = (X₀ * (X₀ * Real.log X₀ + X₀) + 1) * (Real.log X₀) ^ A' := by
          dsimp only [C_small]; ring
        calc X₀ * (X₀ * Real.log X₀ + X₀) * (Real.log x) ^ A'
            ≤ (X₀ * (X₀ * Real.log X₀ + X₀) + 1) * (Real.log X₀) ^ A' := by
              have h1 : X₀ * (X₀ * Real.log X₀ + X₀) ≤ X₀ * (X₀ * Real.log X₀ + X₀) + 1 := by linarith
              exact mul_le_mul h1 hlog_le (by positivity) (by positivity)
          _ = C_small * 3 := hEq.symm
          _ ≤ C_small * x := mul_le_mul_of_nonneg_left hx3 hCsmall_pos.le
      exact (hsum_small.trans hlow).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le) (by positivity))

/-- **Bombieri–Vinogradov Theorem (`x ^ (1/2 : ℝ)` exponent form)**. -/
theorem bombieri_vinogradov_rpow (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊,
          psiAPMaxError q x ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨B, C, hB, hC, hbv⟩ := bombieri_vinogradov A
  refine ⟨B, C, hB, hC, fun x hx => ?_⟩
  rw [← Real.sqrt_eq_rpow]
  exact hbv x hx

/-- **Bombieri–Vinogradov Theorem (Arbitrary Coprime Residue Sequence Form)**. -/
theorem bombieri_vinogradov_residues (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 3 ≤ x →
        ∀ a : ℕ → ℕ, (∀ q : ℕ, 1 ≤ q → Nat.Coprime (a q) q) →
          ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊,
            |Stage2DirichletAP.chebyshevPsiAP q (a q) x - x / (q.totient : ℝ)| ≤
              C * x / (Real.log x) ^ A := by
  obtain ⟨B, C, hB, hC, hbv⟩ := bombieri_vinogradov A
  refine ⟨B, C, hB, hC, fun x hx a ha => ?_⟩
  calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, psiAPMaxError q x :=
          Finset.sum_le_sum fun q hq =>
            abs_chebyshevPsiAP_sub_le_psiAPMaxError (Finset.mem_Icc.mp hq).1
              (ha q (Finset.mem_Icc.mp hq).1) x
    _ ≤ C * x / (Real.log x) ^ A := hbv x hx

/-! ## Section 5: Unconditional Brun–Titchmarsh Inequality (All `1 ≤ q < x`), Selberg Sieve & Master Packaging -/

/-- **Direct Selberg-Sieve Prime Upper Bound via `Stage7SieveMethods.selberg_upper_bound_sieve`**:
for every `N : ℕ` and every sieve level `z ≥ 1`,
`π(N) ≤ z + N / log(z + 1) + z²`. -/
theorem selberg_sieve_prime_bound (N z : ℕ) (hz : 1 ≤ z) :
    (((Finset.Icc 1 N).filter Nat.Prime).card : ℝ) ≤
      (z : ℝ) + (N : ℝ) / Real.log ((z : ℝ) + 1) + (z : ℝ) ^ 2 := by
  let g : ℕ → ℝ := fun n => ((n : ℝ))⁻¹
  have hg : Stage7SieveMethods.IsSelbergDensity g := by
    refine ⟨by simp [g], fun a b => by dsimp only [g]; rw [Nat.cast_mul, mul_inv], fun p hp => ?_⟩
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩
  let A : Finset ℕ := Finset.Icc 1 N
  let R : ℕ → ℝ := fun d => ((A.filter (fun n => d ∣ n)).card : ℝ) - (N : ℝ) * g d
  have hModel : ∀ d : ℕ, Squarefree d →
      ((A.filter (fun n => d ∣ n)).card : ℝ) = (N : ℝ) * g d + R d :=
    fun d _ => by dsimp only [R]; ring
  have hsieve := Stage7SieveMethods.selberg_upper_bound_sieve A hz hg (N : ℝ) R hModel
  -- Bound `|R(d)| ≤ 1` for all `d ≥ 1`
  have hR_le : ∀ d : ℕ, 1 ≤ d → |R d| ≤ 1 := by
    intro d hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hcard_eq : (A.filter (fun n => d ∣ n)).card = N / d := by
      have hbij : A.filter (fun n => d ∣ n) = (Finset.Icc 1 (N / d)).image (fun k => d * k) := by
        ext n
        simp only [A, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hn1, hnN⟩, ⟨k, rfl⟩⟩
          refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by linarith)⟩, rfl⟩
          by_contra hk0
          have hk : k = 0 := by omega
          rw [hk, mul_zero] at hn1; omega
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          exact ⟨⟨Nat.mul_pos hd hk1, (Nat.le_div_iff_mul_le hd).mp hkN |> fun h => by linarith⟩,
            dvd_mul_right d k⟩
      rw [hbij, Finset.card_image_of_injective _ (fun x y hxy => Nat.eq_of_mul_eq_mul_left hd hxy),
        Nat.card_Icc, Nat.add_sub_cancel]
    dsimp only [R, g]
    rw [hcard_eq, ← div_eq_mul_inv]
    have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    have h2 : (N : ℝ) / (d : ℝ) - 1 < ((N / d : ℕ) : ℝ) := by
      have hdiv := Nat.div_add_mod N d
      have hmod : N % d < d := Nat.mod_lt N hd
      have hR : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hdiv
      have hmodR : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]
      nlinarith
    rw [abs_le]; constructor <;> linarith
  -- Lower bound `selbergG g z ≥ log (z + 1)`
  have hG_ge : Real.log ((z : ℝ) + 1) ≤ Stage7SieveMethods.selbergG g z := by
    have hEq : Stage7SieveMethods.selbergG g z =
        ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (r.totient : ℝ) := by
      unfold Stage7SieveMethods.selbergG
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_sqf : Squarefree r := (Finset.mem_filter.mp hr).2
      have hf : Stage7SieveMethods.selbergF g r = (r.totient : ℝ) := by
        unfold Stage7SieveMethods.selbergF
        rw [Stage7SieveMethods.totient_eq_prod_sub_one_of_squarefree hr_sqf, Nat.cast_prod]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        dsimp only [g]
        rw [one_div, inv_inv, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hf]
    rw [hEq]
    exact Stage7SieveMethods.log_add_one_le_sum_squarefree_inv_totient z
  have hlog_pos : 0 < Real.log ((z : ℝ) + 1) := by
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    exact Real.log_pos (by linarith)
  -- Split primes `≤ N` into `p ≤ z` and `p > z` (which are sifted!)
  have hsub : A.filter Nat.Prime ⊆
      Finset.Icc 1 z ∪ A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n) := by
    intro p hp
    simp only [A, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hp ⊢
    by_cases hpz : p ≤ z
    · left; exact ⟨hp.1.1, hpz⟩
    · right
      refine ⟨hp.1, hp.1.1, fun q hqz hq hqp => ?_⟩
      have hEq := (Nat.prime_dvd_prime_iff_eq hq hp.2).mp hqp
      omega
  have hcard_le : ((A.filter Nat.Prime).card : ℝ) ≤
      (z : ℝ) + ((A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n)).card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.Icc 1 z) (A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n))
    have h3 : (Finset.Icc 1 z).card = z := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    have h4 : (A.filter Nat.Prime).card ≤ z + (A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n)).card := by
      omega
    exact_mod_cast h4
  have hrem_le :
      ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree,
        ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree, |R (Nat.lcm d₁ d₂)| ≤ (z : ℝ) ^ 2 := by
    calc _ ≤ ∑ _d₁ ∈ (Finset.Icc 1 z).filter Squarefree,
              ∑ _d₂ ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) := by
            refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
            have h1 : 1 ≤ d₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1
            have h2 : 1 ≤ d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1
            exact hR_le (Nat.lcm d₁ d₂) (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega)))
      _ = (((Finset.Icc 1 z).filter Squarefree).card : ℝ) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul, sq]
      _ ≤ (z : ℝ) ^ 2 := by
            have hle : ((Finset.Icc 1 z).filter Squarefree).card ≤ z := by
              calc _ ≤ (Finset.Icc 1 z).card := Finset.card_filter_le _ _
                _ = z := by rw [Nat.card_Icc, Nat.add_sub_cancel]
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) 2
  have hmain_le : (N : ℝ) / Stage7SieveMethods.selbergG g z ≤ (N : ℝ) / Real.log ((z : ℝ) + 1) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hlog_pos hG_ge
  linarith

/-- Trivial residue-class counting bound: `primeCountAP q a x ≤ ⌊x⌋₊ / q + 1`. -/
private lemma primeCountAP_le_div_add_one {q a : ℕ} (_hq : 0 < q) (x : ℝ) :
    Stage2DirichletAP.primeCountAP q a x ≤ ⌊x⌋₊ / q + 1 := by
  unfold Stage2DirichletAP.primeCountAP
  let S := (Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ a [MOD q]
  have hinj : Set.InjOn (fun p : ℕ => p / q) (S : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ hdiv
    dsimp only at hdiv
    have h1 : p₁ % q = a % q := (Finset.mem_filter.mp hp₁).2.2
    have h2 : p₂ % q = a % q := (Finset.mem_filter.mp hp₂).2.2
    rw [← Nat.div_add_mod p₁ q, ← Nat.div_add_mod p₂ q, hdiv, h1, h2]
  have hsub : S.image (fun p => p / q) ⊆ Finset.range (⌊x⌋₊ / q + 1) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hp_le : p ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hp_le))
  calc S.card = (S.image (fun p => p / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (⌊x⌋₊ / q + 1)).card := Finset.card_le_card hsub
    _ = ⌊x⌋₊ / q + 1 := Finset.card_range _

/-- **UNCONDITIONAL BRUN–TITCHMARSH INEQUALITY FOR ALL `1 ≤ q < x`**:
for EVERY `q ≥ 1`, EVERY `a` with `Nat.Coprime a q`, and EVERY real `x > q`:
`π(x; q, a) ≤ 20 * x / (φ(q) * log(2 * x / q))`. -/
theorem brun_titchmarsh_all {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    {x : ℝ} (hx : (q : ℝ) < x) :
    (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤
      20 * x / ((q.totient : ℝ) * Real.log (2 * x / (q : ℝ))) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hphi_le : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hx_pos : 0 < x := hq_pos.trans hx
  have h2xq_gt2 : 2 < 2 * x / (q : ℝ) := by
    rw [lt_div_iff₀ hq_pos]; linarith
  have hlog2xq_pos : 0 < Real.log (2 * x / (q : ℝ)) := Real.log_pos (by linarith)
  by_cases h10 : 10 * (q : ℝ) ≤ x
  · -- Large ratio `x ≥ 10 * q`: apply `Stage7SieveMethods.brun_titchmarsh_primeCountAP`
    set N : ℕ := ⌊x⌋₊
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hN_ge : 9 * q ≤ N := by
      have h1 : (9 * q : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      exact h1
    have hN_le_x : (N : ℝ) ≤ x := Nat.floor_le hx_pos.le
    have hbt := Stage7SieveMethods.brun_titchmarsh_primeCountAP hq hcop 0 N hN_ge
    have hzero : Stage2DirichletAP.primeCountAP q a (0 : ℝ) = 0 := by
      unfold Stage2DirichletAP.primeCountAP
      simp only [Nat.floor_zero, zero_add, Finset.range_one, Finset.filter_singleton]
      rw [if_neg (fun h => Nat.not_prime_zero h.1), Finset.card_empty]
    have hpi_eq : Stage2DirichletAP.primeCountAP q a x =
        Stage2DirichletAP.primeCountAP q a ((0 + N : ℕ) : ℝ) := by
      simp [Stage2DirichletAP.primeCountAP, N]
    rw [Nat.cast_zero, hzero, Nat.sub_zero, ← hpi_eq] at hbt
    have hNq_ge9 : 9 ≤ (N : ℝ) / (q : ℝ) := (le_div_iff₀ hq_pos).mpr (by exact_mod_cast hN_ge)
    have hlogNq_pos : 0 < Real.log ((N : ℝ) / (q : ℝ)) := Real.log_pos (by linarith)
    have hlog_cmp : Real.log (2 * x / (q : ℝ)) ≤ 2 * Real.log ((N : ℝ) / (q : ℝ)) := by
      have hN_gt : (9 / 10 : ℝ) * x ≤ (N : ℝ) := by
        have hlt := Nat.lt_floor_add_one x
        linarith
      have hsq : 2 * x / (q : ℝ) ≤ ((N : ℝ) / (q : ℝ)) ^ 2 := by
        have h1 : (9 / 10 : ℝ) * (x / (q : ℝ)) ≤ (N : ℝ) / (q : ℝ) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hN_gt hq_pos.le
        have h2 : 9 * ((9 / 10 : ℝ) * (x / (q : ℝ))) ≤ ((N : ℝ) / (q : ℝ)) * ((N : ℝ) / (q : ℝ)) :=
          mul_le_mul hNq_ge9 h1 (by positivity) (by positivity)
        rw [← sq] at h2
        have h3 : 2 * x / (q : ℝ) ≤ 9 * ((9 / 10 : ℝ) * (x / (q : ℝ))) := by
          have : 0 ≤ x / (q : ℝ) := by positivity
          have hEq1 : 2 * x / (q : ℝ) = 2 * (x / (q : ℝ)) := by ring
          linarith
        exact h3.trans h2
      have h := Real.log_le_log (by positivity) hsq
      rwa [Real.log_pow] at h
    calc (Stage2DirichletAP.primeCountAP q a x : ℝ)
        ≤ 10 * (N : ℝ) / ((q.totient : ℝ) * Real.log ((N : ℝ) / (q : ℝ))) := hbt
      _ ≤ 10 * x / ((q.totient : ℝ) * (Real.log (2 * x / (q : ℝ)) / 2)) := by
          refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
          exact mul_le_mul_of_nonneg_left (by linarith) hphi_pos.le
      _ = 20 * x / ((q.totient : ℝ) * Real.log (2 * x / (q : ℝ))) := by
          field_simp [hphi_pos.ne', hlog2xq_pos.ne']; ring
  · -- Small ratio `q < x < 10 * q`: elementary residue-class counting
    push Not at h10
    have hlog_le4 : Real.log (2 * x / (q : ℝ)) ≤ 4 := by
      have hlt20 : 2 * x / (q : ℝ) ≤ 20 := (div_le_iff₀ hq_pos).mpr (by linarith)
      have h20_le : (20 : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ) := by norm_num
      have h := Real.log_le_log (by positivity) (hlt20.trans h20_le)
      rw [Real.log_pow] at h
      have hl2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
      push_cast at h; linarith
    have hcnt : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ 2 * x / (q : ℝ) := by
      have h1 : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ ((⌊x⌋₊ / q : ℕ) : ℝ) + 1 := by
        exact_mod_cast primeCountAP_le_div_add_one hq x
      have h2 : ((⌊x⌋₊ / q : ℕ) : ℝ) ≤ x / (q : ℝ) :=
        Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hx_pos.le) hq_pos.le)
      have h3 : (1 : ℝ) ≤ x / (q : ℝ) := (one_le_div hq_pos).mpr hx.le
      have h4 : x / (q : ℝ) + x / (q : ℝ) = 2 * x / (q : ℝ) := by ring
      linarith
    calc (Stage2DirichletAP.primeCountAP q a x : ℝ)
        ≤ 2 * x / (q : ℝ) := hcnt
      _ ≤ 2 * x / (q.totient : ℝ) := div_le_div_of_nonneg_left (by positivity) hphi_pos hphi_le
      _ ≤ 20 * x / ((q.totient : ℝ) * Real.log (2 * x / (q : ℝ))) := by
          rw [div_le_div_iff₀ hphi_pos (mul_pos hphi_pos hlog2xq_pos)]
          have : 2 * x * Real.log (2 * x / (q : ℝ)) ≤ 20 * x := by nlinarith
          have hEq1 : 2 * x * ((q.totient : ℝ) * Real.log (2 * x / (q : ℝ))) =
              (q.totient : ℝ) * (2 * x * Real.log (2 * x / (q : ℝ))) := by ring
          have hEq2 : 20 * x * (q.totient : ℝ) = (q.totient : ℝ) * (20 * x) := by ring
          rw [hEq1, hEq2]
          exact mul_le_mul_of_nonneg_left this hphi_pos.le

open Classical in
/-- **MASTER UNCONDITIONAL STAGE 11 BOMBIERI–VINOGRADOV & VAUGHAN PACKAGE (`0` ASSUMPTIONS!)**:
simultaneously packages:
1. Exact unconditional Vaughan's Identity (1977) for `Λ(n)` (`vaughan_identity`),
2. Exact unconditional Multiplicative Large Sieve Inequality weighted by `q / φ(q)` (`multiplicative_large_sieve_Ioc`),
3. Unconditional Pólya–Vinogradov Inequality for primitive characters (`polya_vinogradov_primitive`),
4. Full Unconditional Bombieri–Vinogradov Theorem at level of distribution `ϑ = 1/2` (`bombieri_vinogradov_rpow`),
5. Full Unconditional Brun–Titchmarsh Inequality for all `1 ≤ q < x` (`brun_titchmarsh_all`). -/
theorem stage11_bombieri_vinogradov_master :
    (∀ {U V n : ℕ}, 1 ≤ U → 1 ≤ n →
      Λ n = vaughanA0 V n + vaughanA1 U n - vaughanA2 U V n - vaughanA3 U V n) ∧
    (∀ (Q M N : ℕ) (a : ℕ → ℂ),
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
        ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) ∧
    (∀ {d : ℕ} [NeZero d], 2 ≤ d → ∀ {χ : DirichletCharacter ℂ d}, χ.IsPrimitive → ∀ N : ℕ,
      ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ ≤ Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) ∧
    (∀ A : ℝ, ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊,
          psiAPMaxError q x ≤ C * x / (Real.log x) ^ A) ∧
    (∀ {q a : ℕ}, 0 < q → Nat.Coprime a q → ∀ {x : ℝ}, (q : ℝ) < x →
      (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤
        20 * x / ((q.totient : ℝ) * Real.log (2 * x / (q : ℝ)))) :=
  ⟨fun hU hn => vaughan_identity hU hn,
   multiplicative_large_sieve_Ioc,
   fun {_ _} hd2 {_} hprim N => polya_vinogradov_primitive hd2 hprim N,
   bombieri_vinogradov_rpow,
   fun {_ _} hq hcop {_} hx => brun_titchmarsh_all hq hcop hx⟩

end RHDirect.Stage11BombieriVinogradov
