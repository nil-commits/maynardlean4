import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage7PNTInAP
import RHDirect.Stage7SiegelWalfisz
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage2DirichletAP
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# RHDirect.Stage8BarbanDavenport

100%-unconditional (`0` `sorry`, `0` custom `axiom`, `0` warnings, `0` info) formalization of the
**Barban–Davenport–Halberstam Mean-Square Theorem for Primes in Arithmetic Progressions**,
**Siegel's Theorem**, **Siegel–Walfisz Theorem**, and **Almost-All-Moduli PNT in AP** directly on
Mathlib's `DirichletCharacter.LFunction`, `Stage2DirichletAP.chebyshevPsiAP`, and
`Stage2DirichletAP.chebyshevPsiChar` in pure Mathlib `v4.33.1`.
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage8BarbanDavenport

/-! ## Section 1: Primitive-Induction Transfer, Divisor Averaging & Dyadic Large-Sieve Variance -/

/-- If `d ∣ q` and `Nat.Coprime n q`, then `(changeLevel hd ψ) (n : ZMod q) = ψ (n : ZMod d)`. -/
theorem changeLevel_apply_nat_of_coprime {d q : ℕ} (hd : d ∣ q)
    (ψ : DirichletCharacter ℂ d) {n : ℕ} (hcop : Nat.Coprime n q) :
    DirichletCharacter.changeLevel hd ψ (n : ZMod q) = ψ (n : ZMod d) := by
  have hu : IsUnit (n : ZMod q) := Stage2DirichletAP.isUnit_zmod_of_coprime hcop
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd hu.unit
  have hspec : ((hu.unit : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) := hu.unit_spec
  rw [hspec, ZMod.cast_natCast hd] at h1
  exact h1

/-- For any non-principal Dirichlet character `χ : DirichletCharacter ℂ q`, its conductor satisfies
`3 ≤ χ.conductor`. -/
theorem three_le_conductor_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 3 ≤ χ.conductor := by
  have hne0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
  have hne1 : χ.conductor ≠ 1 := by
    intro h1
    apply hχ
    have hprim := χ.changeLevel_primitiveCharacter
    have hψ1 : χ.primitiveCharacter = 1 := by
      have : NeZero χ.conductor := ⟨hne0⟩
      have hcard : Fintype.card (ZMod χ.conductor)ˣ = 1 := by
        rw [ZMod.card_units_eq_totient, h1]; norm_num
      have hsub : Subsingleton (ZMod χ.conductor)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      ext u
      rw [Subsingleton.elim u 1]
      simp
    rw [← hprim, hψ1, map_one]
  have hne2 : χ.conductor ≠ 2 := by
    intro h2
    have hprim_is := χ.primitiveCharacter_isPrimitive
    have : NeZero χ.conductor := ⟨hne0⟩
    have hψ1 : χ.primitiveCharacter = 1 := by
      have hcard : Fintype.card (ZMod χ.conductor)ˣ = 1 := by
        rw [ZMod.card_units_eq_totient, h2]; norm_num
      have hsub : Subsingleton (ZMod χ.conductor)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      ext u
      rw [Subsingleton.elim u 1]
      simp
    have hc : χ.primitiveCharacter.conductor = χ.conductor := hprim_is
    rw [hψ1, DirichletCharacter.conductor_one] at hc
    omega
  omega

/-- Counting bound for primes dividing `q` that do not divide a divisor `d ≥ 3` of `q`:
`#({p ∈ q.primeFactors | ¬ p ∣ d}) ≤ Real.log q`. -/
theorem card_primeFactors_not_dvd_le_log {q d : ℕ} (hq : 0 < q) (hd3 : 3 ≤ d) (hdq : d ∣ q) :
    ((q.primeFactors.filter (fun p => ¬ p ∣ d)).card : ℝ) ≤ Real.log (q : ℝ) := by
  set S : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ∣ d)
  have hS_cop : Nat.Coprime (∏ p ∈ S, p) d := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hmem := Finset.mem_filter.mp hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hmem.1
    exact (Nat.Prime.coprime_iff_not_dvd hpr).mpr hmem.2
  have hS_dvd : (∏ p ∈ S, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd q)
  have hmul_dvd : d * (∏ p ∈ S, p) ∣ q := (hS_cop.symm).mul_dvd_of_dvd_of_dvd hdq hS_dvd
  have hmul_le : ((d : ℝ) * ∏ p ∈ S, (p : ℝ)) ≤ (q : ℝ) := by
    have hnat : d * ∏ p ∈ S, p ≤ q := Nat.le_of_dvd hq hmul_dvd
    rw [← Nat.cast_prod, ← Nat.cast_mul]
    exact_mod_cast hnat
  have hprod_pos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) :=
    Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlog_ge : Real.log (d : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    have h1 := Real.log_le_log (mul_pos hd_pos hprod_pos) hmul_le
    rw [Real.log_mul hd_pos.ne' hprod_pos.ne',
      Real.log_prod fun p hp => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos).ne'] at h1
    exact h1
  have hlog3_gt1 : (1 : ℝ) < Real.log (3 : ℝ) := by
    have he3 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) he3)
  have hlogd_ge1 : (1 : ℝ) ≤ Real.log (d : ℝ) :=
    hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hd3))
  by_cases h2 : 2 ∈ S
  · have hsum_split : ∑ p ∈ S, Real.log (p : ℝ) = Real.log 2 + ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
      rw [← Finset.add_sum_erase S (fun p => Real.log (p : ℝ)) h2]
      norm_num
    have herase_ge : ((S.erase 2).card : ℝ) ≤ ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
      calc ((S.erase 2).card : ℝ)
          = ∑ _p ∈ S.erase 2, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
            have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
            have hp3 : 3 ≤ p := by have := hpr.two_le; omega
            exact hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hp3))
    have hcard_eq : (S.card : ℝ) = ((S.erase 2).card : ℝ) + 1 := by
      have hnat : (S.erase 2).card + 1 = S.card := Finset.card_erase_add_one h2
      exact_mod_cast hnat.symm
    have hlog2_nn : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  · have hsum_ge : (S.card : ℝ) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      calc (S.card : ℝ)
          = ∑ _p ∈ S, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
            have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hp3 : 3 ≤ p := by have := hpr.two_le; omega
            exact hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hp3))
    linarith

private lemma sum_biUnion_le_of_nonneg_local {α β : Type*} [DecidableEq β] (s : Finset α)
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

/-- **Exact Primitive-Induction Character-Sum Transfer**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
and EVERY `x ≥ 1`,
`‖chebyshevPsiChar χ x - chebyshevPsiChar χ.primitiveCharacter x‖ ≤ Real.log q * Real.log x`. -/
theorem norm_chebyshevPsiChar_sub_primitive_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖Stage2DirichletAP.chebyshevPsiChar χ x -
        Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤
      Real.log (q : ℝ) * Real.log x := by
  set d : ℕ := χ.conductor
  set ψ : DirichletCharacter ℂ d := χ.primitiveCharacter
  have hdq : d ∣ q := χ.conductor_dvd_level
  have hch : DirichletCharacter.changeLevel hdq ψ = χ := χ.changeLevel_primitiveCharacter
  have hd3 : 3 ≤ d := three_le_conductor_of_ne_one hχ
  have hdiff_eq :
      Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar ψ x =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (χ (n : ZMod q) - ψ (n : ZMod d)) * (Λ n : ℂ) := by
    unfold Stage2DirichletAP.chebyshevPsiChar
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hdiff_eq]
  set T : Finset ℕ :=
    (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ Nat.Coprime n d ∧ IsPrimePow n)
  have hnorm_le :
      ‖∑ n ∈ Finset.range (⌊x⌋₊ + 1), (χ (n : ZMod q) - ψ (n : ZMod d)) * (Λ n : ℂ)‖ ≤
        ∑ n ∈ T, Λ n := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hpp : IsPrimePow n
    · by_cases hcopq : Nat.Coprime n q
      · have hval : χ (n : ZMod q) = ψ (n : ZMod d) := by
          rw [← hch]
          exact changeLevel_apply_nat_of_coprime hdq ψ hcopq
        rw [hval, sub_self, zero_mul, norm_zero]
        split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl]
      · by_cases hcopd : Nat.Coprime n d
        · rw [if_pos ⟨hcopq, hcopd, hpp⟩]
          have hχ0 : χ (n : ZMod q) = 0 :=
            MulChar.map_nonunit χ fun hu => hcopq ((ZMod.isUnit_iff_coprime n q).mp hu)
          rw [hχ0, zero_sub, norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact (mul_le_mul_of_nonneg_right (ψ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
        · have hχ0 : χ (n : ZMod q) = 0 :=
            MulChar.map_nonunit χ fun hu => hcopq ((ZMod.isUnit_iff_coprime n q).mp hu)
          have hψ0 : ψ (n : ZMod d) = 0 :=
            MulChar.map_nonunit ψ fun hu => hcopd ((ZMod.isUnit_iff_coprime n d).mp hu)
          rw [hχ0, hψ0, sub_self, zero_mul, norm_zero, if_neg (fun h => hcopd h.2.1)]
    · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
      rw [h0, Complex.ofReal_zero, mul_zero, norm_zero, if_neg (fun h => hpp h.2.2)]
  set S : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ∣ d)
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsub : T ⊆ S.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [T, S, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnle, hncopq, hcopd, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      exact hncopq (((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).pow_left k)
    have hnpd : ¬ p ∣ d := by
      intro hpd
      have hdiv : p ∣ (p ^ k).gcd d := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpd
      rw [hcopd.gcd_eq_one] at hdiv
      exact hp.not_dvd_one hdiv
    refine ⟨p, ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩, hnpd⟩, k, ⟨hkpos, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hT_le : ∑ n ∈ T, Λ n ≤ (S.card : ℝ) * Real.log x := by
    calc ∑ n ∈ T, Λ n
        ≤ ∑ n ∈ S.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ ∑ p ∈ S, ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
          sum_biUnion_le_of_nonneg_local _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ ≤ ∑ _p ∈ S, Real.log x := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          calc ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n
              ≤ ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Λ (p ^ k) :=
                Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
            _ = ∑ _k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log (p : ℝ) := by
                refine Finset.sum_congr rfl fun k hk => ?_
                have hk0 : k ≠ 0 := by rw [Finset.mem_Icc] at hk; omega
                rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
                  ArithmeticFunction.vonMangoldt_apply_prime hpr]
            _ = ((Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card : ℝ) * Real.log (p : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
                have hcard : (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card ≤ Nat.log p ⌊x⌋₊ := by
                  rw [Nat.card_Icc]; omega
                exact_mod_cast hcard
            _ = Real.log ((p : ℝ) ^ Nat.log p ⌊x⌋₊) := (Real.log_pow (p : ℝ) _).symm
            _ ≤ Real.log x := by
                have hpow : p ^ Nat.log p ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p (by omega)
                exact Real.log_le_log (pow_pos (Nat.cast_pos.mpr hpr.pos) _)
                  ((by exact_mod_cast hpow : ((p : ℝ) ^ Nat.log p ⌊x⌋₊) ≤ (⌊x⌋₊ : ℝ)).trans hNx)
      _ = (S.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
  exact (hnorm_le.trans hT_le).trans
    (mul_le_mul_of_nonneg_right (card_primeFactors_not_dvd_le_log (NeZero.pos q) hd3 hdq)
      (Real.log_nonneg hx))

/-- Super-multiplicativity of Euler's totient: `φ(d) * φ(m) ≤ φ(d * m)` for all `d, m : ℕ`. -/
theorem totient_mul_ge_mul_totient (d m : ℕ) : d.totient * m.totient ≤ (d * m).totient :=
  Nat.totient_super_multiplicative d m

/-- Exact reciprocal-totient expansion: for every `m ≥ 1`,
`(m : ℝ) / (m.totient : ℝ) = ∑ s ∈ m.primeFactors.powerset, ∏ p ∈ s, ((p : ℝ) - 1)⁻¹`. -/
theorem div_totient_eq_sum_powerset {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) =
      ∑ s ∈ m.primeFactors.powerset, ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
  have htot := Nat.totient_eq_mul_prod_factors m
  have htotR : (m.totient : ℝ) = (m : ℝ) * ∏ p ∈ m.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    have hq := congrArg (Rat.cast : ℚ → ℝ) htot
    simpa [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one] using hq
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hprod_eq : (m : ℝ) / (m.totient : ℝ) = ∏ p ∈ m.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) := by
    rw [htotR, div_mul_eq_div_div, div_self hm_pos.ne', one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    field_simp [(by linarith : (p : ℝ) ≠ 0), (by linarith : (p : ℝ) - 1 ≠ 0)]
    ring
  rw [hprod_eq, Finset.prod_one_add]

/-- Elementary telescoping bound `∑ k ∈ Finset.Icc 2 M, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ ≤ 1`. -/
private lemma sum_inv_mul_sub_one_le_one (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ ≤ 1 := by
  by_cases hM : M < 2
  · have : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]; norm_num
  · push Not at hM
    have hstrong : ∀ n : ℕ, 2 ≤ n →
        ∑ k ∈ Finset.Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ = 1 - (n : ℝ)⁻¹ := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        have h2 : Finset.Icc 2 2 = {2} := by ext x; simp
        rw [h2, Finset.sum_singleton]; norm_num
      | succ k hk ih =>
        have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        push_cast
        have hsub1 : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
        rw [hsub1]
        field_simp [hk_pos.ne', (by linarith : (k : ℝ) + 1 ≠ 0)]
        ring
    rw [hstrong M hM]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) M)]

/-- **Exact Reciprocal-Totient Sum Bound**:
for EVERY `M ≥ 1`, `∑ m ∈ Finset.Icc 1 M, (m.totient : ℝ)⁻¹ ≤ 6 * Real.log (2 * (M : ℝ))`. -/
theorem sum_inv_totient_le_log {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (m.totient : ℝ)⁻¹ ≤ 6 * Real.log (2 * (M : ℝ)) := by
  set P : Finset ℕ := (Finset.Icc 1 M).filter Nat.Prime
  set H : ℝ := ∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹
  have hH_le : H ≤ 2 * Real.log (2 * (M : ℝ)) := by
    have h1 := Stage5DirichletLZeroFree.harmonic_sum_le_log_add_one hM
    have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hlog2M : Real.log (2 * (M : ℝ)) = Real.log 2 + Real.log (M : ℝ) :=
      Real.log_mul (by norm_num) hM_pos.ne'
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogM_nn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    linarith
  have hstep1 :
      ∑ m ∈ Finset.Icc 1 M, (m.totient : ℝ)⁻¹ =
        ∑ m ∈ Finset.Icc 1 M,
          ∑ s ∈ P.powerset,
            if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_le : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hmR_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hexp := div_totient_eq_sum_powerset hm_pos
    have hinv : (m.totient : ℝ)⁻¹ = ((m : ℝ))⁻¹ * ((m : ℝ) / (m.totient : ℝ)) := by
      field_simp [hmR_pos.ne']
    rw [hinv, hexp, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext s
    simp only [Finset.mem_powerset, Finset.mem_filter, P]
    constructor
    · intro hs
      refine ⟨fun p hp => ?_, ?_⟩
      · have hmem := hs hp
        have hpr : p.Prime := Nat.prime_of_mem_primeFactors hmem
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, (Nat.le_of_dvd hm_pos hpm).trans hm_le⟩, hpr⟩
      · exact (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans (Nat.prod_primeFactors_dvd m)
    · rintro ⟨hsP, hdvd⟩ p hp
      have hpr : p.Prime := (Finset.mem_filter.mp (hsP hp)).2
      have hpm : p ∣ m := (Finset.dvd_prod_of_mem _ hp).trans hdvd
      exact Nat.mem_primeFactors.mpr ⟨hpr, hpm, hm_pos.ne'⟩
  rw [hstep1, Finset.sum_comm]
  have hinner : ∀ s ∈ P.powerset,
      ∑ m ∈ Finset.Icc 1 M,
          (if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0) ≤
        H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro s hs
    set r : ℕ := ∏ p ∈ s, p
    have hr_pos : 0 < r := Finset.prod_pos fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2.pos
    have hrR_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_pos
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hbij :
        ∑ m ∈ (Finset.Icc 1 M).filter (fun m => r ∣ m), ((m : ℝ))⁻¹ =
          ((r : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / r) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
        obtain ⟨⟨hm1, hmM⟩, ⟨k, hk⟩⟩ := hm
        have hk1 : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0, mul_zero] at hk
          omega
        rw [hk, Nat.mul_div_cancel_left _ hr_pos]
        exact ⟨hk1, (Nat.le_div_iff_mul_le hr_pos).mpr (by rw [mul_comm]; omega)⟩
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [Finset.mem_filter] at hm₁ hm₂
        have h1 : r * (m₁ / r) = m₁ := Nat.mul_div_cancel' hm₁.2
        have h2 : r * (m₂ / r) = m₂ := Nat.mul_div_cancel' hm₂.2
        rw [← h1, ← h2, h]
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨r * k, ?_, Nat.mul_div_cancel_left k hr_pos⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos hr_pos hk.1, ?_⟩, dvd_mul_right r k⟩
        exact (Nat.le_div_iff_mul_le hr_pos).mp hk.2 |> fun h => by rwa [mul_comm] at h
      · intro m hm
        simp only [Finset.mem_filter] at hm
        have h1 : (r : ℝ) * ((m / r : ℕ) : ℝ) = (m : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' hm.2
        rw [← h1, mul_inv]
    have hHsub : ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹ ≤ H := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self M r)
    have hprod_nn : 0 ≤ ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ :=
      Finset.prod_nonneg fun p hp => by
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
        exact inv_nonneg.mpr (by linarith)
    have hprod_merge :
        ((r : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ = ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
      have hr_cast : (r : ℝ) = ∏ p ∈ s, (p : ℝ) := by simp [r]
      rw [hr_cast, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => (mul_inv _ _).symm
    calc (∑ m ∈ (Finset.Icc 1 M).filter (fun m => r ∣ m), ((m : ℝ))⁻¹) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹
        = (((r : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
          rw [hbij]
      _ ≤ (((r : ℝ))⁻¹ * H) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by gcongr
      _ = H * (((r : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹) := by ring
      _ = H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by rw [hprod_merge]
  have hprod_le3 : ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) ≤ 3 := by
    calc ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹)
        ≤ ∏ p ∈ P, Real.exp (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
          · have hpr : p.Prime := (Finset.mem_filter.mp hp).2
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
            have hnn : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := inv_nonneg.mpr (by nlinarith)
            linarith
          · linarith [Real.add_one_le_exp (((p : ℝ) * ((p : ℝ) - 1))⁻¹)]
      _ = Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑ k ∈ Finset.Icc 2 M, ((k : ℝ) * ((k : ℝ) - 1))⁻¹) := by
          apply Real.exp_le_exp.mpr
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k hk _ => ?_
          · intro p hp
            have hmem := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr ⟨hmem.2.two_le, (Finset.mem_Icc.mp hmem.1).2⟩
          · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
            exact inv_nonneg.mpr (by nlinarith)
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (sum_inv_mul_sub_one_le_one M)
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc ∑ s ∈ P.powerset,
          ∑ m ∈ Finset.Icc 1 M,
            (if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0)
      ≤ ∑ s ∈ P.powerset, H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.sum_le_sum hinner
    _ = H * ∑ s ∈ P.powerset, ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := (Finset.mul_sum _ _ _).symm
    _ = H * ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by rw [Finset.prod_one_add]
    _ ≤ (2 * Real.log (2 * (M : ℝ))) * 3 :=
        mul_le_mul hH_le hprod_le3 (Finset.prod_nonneg fun p hp => by
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
          have hnn : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := inv_nonneg.mpr (by nlinarith)
          linarith) (by
          have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          have : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by linarith)
          linarith)
    _ = 6 * Real.log (2 * (M : ℝ)) := by ring

/-- **Exact Divisor-Averaging Inequality**:
for ALL `1 ≤ d ≤ Q`,
`∑_{q ≤ Q, d ∣ q} 1 / φ(q) ≤ (6 / φ(d)) * Real.log (2 * Q / d)`. -/
theorem sum_inv_totient_dvd_le {d Q : ℕ} (hd : 1 ≤ d) (hdQ : d ≤ Q) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ ≤
      (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
  have hd_pos : 0 < d := hd
  have hM : 1 ≤ Q / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)
  have hphi_d_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd_pos)
  have hbij :
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ =
        ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹ := by
    refine Finset.sum_bij (fun q _ => q / d) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      obtain ⟨⟨hq1, hqQ⟩, ⟨m, hm⟩⟩ := hq
      have hm1 : 1 ≤ m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        rw [hm0, mul_zero] at hm
        omega
      rw [hm, Nat.mul_div_cancel_left _ hd_pos]
      exact ⟨hm1, (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; omega)⟩
    · intro q₁ hq₁ q₂ hq₂ h
      simp only [Finset.mem_filter] at hq₁ hq₂
      rw [← Nat.mul_div_cancel' hq₁.2, ← Nat.mul_div_cancel' hq₂.2, h]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd_pos⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd_pos hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd_pos).mp hm.2
      rwa [mul_comm] at this
    · intro q hq
      simp only [Finset.mem_filter] at hq
      rw [Nat.mul_div_cancel' hq.2]
  rw [hbij]
  have hstep :
      ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹ ≤
        (d.totient : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 (Q / d), (m.totient : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hphi_m_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm_pos)
    have hmul : (d.totient : ℝ) * (m.totient : ℝ) ≤ ((d * m).totient : ℝ) := by
      exact_mod_cast totient_mul_ge_mul_totient d m
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hphi_d_pos hphi_m_pos) hmul
  have hlog_le : Real.log (2 * ((Q / d : ℕ) : ℝ)) ≤ Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
    have hdiv_le : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hpos : (0 : ℝ) < 2 * ((Q / d : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((Q / d : ℕ) : ℝ) := by exact_mod_cast hM
      linarith
    exact Real.log_le_log hpos (by linarith [show 2 * ((Q : ℝ) / (d : ℝ)) = 2 * (Q : ℝ) / (d : ℝ) by ring])
  calc ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹
      ≤ (d.totient : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 (Q / d), (m.totient : ℝ)⁻¹ := hstep
    _ ≤ (d.totient : ℝ)⁻¹ * (6 * Real.log (2 * ((Q / d : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_inv_totient_le_log hM) (inv_nonneg.mpr hphi_d_pos.le)
    _ ≤ (d.totient : ℝ)⁻¹ * (6 * Real.log (2 * (Q : ℝ) / (d : ℝ))) := by
        gcongr
    _ = (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := by ring

/-- Elementary geometric sum `∑ j ∈ Finset.range n, (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n`. -/
private lemma sum_two_pow_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- Elementary geometric sum `∑ j ∈ Finset.range n, ((2 : ℝ) ^ j)⁻¹ ≤ 2`. -/
private lemma sum_inv_two_pow_le_two (n : ℕ) :
    ∑ j ∈ Finset.range n, ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
  have hstrong : ∀ m : ℕ, ∑ j ∈ Finset.range m, ((2 : ℝ) ^ j)⁻¹ = 2 - ((2 : ℝ) ^ m)⁻¹ * 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
      field_simp [hne]
      ring
  rw [hstrong n]
  have : 0 ≤ ((2 : ℝ) ^ n)⁻¹ * 2 := by positivity
  linarith

open Classical in
/-- **Unconditional Dyadic Large-Sieve Primitive-Character Mean-Square Bound**:
for ALL `1 ≤ Q₁ ≤ Q` and `x ≥ 4`:
`∑ d ∈ Finset.Ioc Q₁ Q, (1 / φ(d)) * ∑*_{χ mod d} ‖ψ(x, χ)‖² ≤ 144 * x * Q * log x + 12 * x² * log x / Q₁`. -/
theorem prim_variance_Ioc_unweighted_le {Q₁ Q : ℕ} (hQ₁ : 1 ≤ Q₁) (hQ : Q₁ ≤ Q)
    {x : ℝ} (hx : 4 ≤ x) :
    ∑ d ∈ Finset.Ioc Q₁ Q,
        (d.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
      144 * x * (Q : ℝ) * Real.log x + 12 * x ^ 2 * Real.log x / (Q₁ : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hQ₁_pos : (0 : ℝ) < (Q₁ : ℝ) := Nat.cast_pos.mpr hQ₁
  by_cases heq : Q₁ = Q
  · subst heq
    rw [Finset.Ioc_self, Finset.sum_empty]
    positivity
  · have hlt : Q₁ < Q := lt_of_le_of_ne hQ heq
    have hdiv_ge1 : 1 ≤ Q / Q₁ := (Nat.le_div_iff_mul_le hQ₁).mpr (by omega)
    set J : ℕ := Nat.log 2 (Q / Q₁)
    have hJ_le : Q₁ * 2 ^ J ≤ Q := by
      have h1 : 2 ^ J ≤ Q / Q₁ := Nat.pow_log_le_self 2 (by omega)
      exact (Nat.le_div_iff_mul_le hQ₁).mp h1 |> fun h => by rwa [mul_comm] at h
    have hJ_gt : Q < Q₁ * 2 ^ (J + 1) := by
      have h1 : Q / Q₁ < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Q / Q₁)
      have h2 := Nat.div_lt_iff_lt_mul hQ₁ |>.mp h1
      linarith [mul_comm (2 ^ (J + 1)) Q₁]
    set f : ℕ → ℝ := fun d =>
      (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
    have hf_nn : ∀ d, 0 ≤ f d := fun d =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hcover : Finset.Ioc Q₁ Q ⊆
        (Finset.range (J + 1)).biUnion (fun j => Finset.Ioc (Q₁ * 2 ^ j) (Q₁ * 2 ^ (j + 1))) := by
      intro d hd
      simp only [Finset.mem_Ioc, Finset.mem_biUnion, Finset.mem_range] at hd ⊢
      set j : ℕ := Nat.log 2 ((d - 1) / Q₁)
      have hdm1 : 1 ≤ (d - 1) / Q₁ := (Nat.le_div_iff_mul_le hQ₁).mpr (by omega)
      have hdm1_le : (d - 1) / Q₁ ≤ Q / Q₁ := Nat.div_le_div_right (by omega)
      have hj_le : j ≤ J := Nat.log_mono_right hdm1_le
      have hlo : Q₁ * 2 ^ j ≤ d - 1 := by
        have h1 : 2 ^ j ≤ (d - 1) / Q₁ := Nat.pow_log_le_self 2 (by omega)
        have h2 := (Nat.le_div_iff_mul_le hQ₁).mp h1
        rwa [mul_comm] at h2
      have hhi : d - 1 < Q₁ * 2 ^ (j + 1) := by
        have h1 : (d - 1) / Q₁ < 2 ^ (j + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((d - 1) / Q₁)
        have h2 := (Nat.div_lt_iff_lt_mul hQ₁).mp h1
        rwa [mul_comm] at h2
      exact ⟨j, by omega, by omega, by omega⟩
    have hblock : ∀ j : ℕ,
        ∑ d ∈ Finset.Ioc (Q₁ * 2 ^ j) (Q₁ * 2 ^ (j + 1)), f d ≤
          (6 * x * Real.log x) *
            (x / ((Q₁ : ℝ) * (2 : ℝ) ^ j) + 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j)) := by
      intro j
      set A : ℕ := Q₁ * 2 ^ j
      have hA_pos : 0 < A := Nat.mul_pos hQ₁ (pow_pos (by norm_num) j)
      have hAR_pos : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA_pos
      have h2A : Q₁ * 2 ^ (j + 1) = 2 * A := by dsimp only [A]; ring
      rw [h2A]
      have h1 : ∑ d ∈ Finset.Ioc A (2 * A), f d ≤
          (A : ℝ)⁻¹ * ∑ d ∈ Finset.Icc 1 (2 * A),
            ((d : ℝ) / (d.totient : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 := by
        rw [Finset.mul_sum]
        calc ∑ d ∈ Finset.Ioc A (2 * A), f d
            ≤ ∑ d ∈ Finset.Ioc A (2 * A),
                (A : ℝ)⁻¹ * (((d : ℝ) / (d.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                    ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) := by
              refine Finset.sum_le_sum fun d hd => ?_
              have hd_gt : A < d := (Finset.mem_Ioc.mp hd).1
              have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
              have hA_le_d : (A : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_gt.le
              have hinv_le : (d.totient : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ * ((d : ℝ) / (d.totient : ℝ)) := by
                have h1 : (1 : ℝ) ≤ (A : ℝ)⁻¹ * (d : ℝ) := by
                  rw [← div_eq_inv_mul, one_le_div hAR_pos]; exact hA_le_d
                have h2 := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (Nat.cast_nonneg d.totient))
                simpa [div_eq_mul_inv, mul_assoc] using h2
              dsimp only [f]
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right hinv_le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          _ ≤ ∑ d ∈ Finset.Icc 1 (2 * A),
                (A : ℝ)⁻¹ * (((d : ℝ) / (d.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                    ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ?_
              · intro d hd
                simp only [Finset.mem_Ioc, Finset.mem_Icc] at hd ⊢; omega
              · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                  (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      have hshift :
          ∑ d ∈ Finset.Icc 1 (2 * A),
              ((d : ℝ) / (d.totient : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 =
            ∑ k ∈ Finset.range (2 * A),
              (((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 := by
        refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
        · intro d hd; simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢; omega
        · intro d₁ hd₁ d₂ hd₂ h; simp only [Finset.mem_Icc] at hd₁ hd₂; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hsub : d - 1 + 1 = d := by omega
          let F : ℕ → ℝ := fun n =>
            ((n : ℝ) / (n.totient : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
          exact (congrArg F hsub).symm
      have hLS := Stage3BombieriVinogradov.prim_chebyshevPsiChar_mean_square_le (2 * A) hx1
      have hpsi : chebyshevPsi x ≤ 6 * x := Stage4ExplicitFormula.chebyshevPsi_le_six_mul hx1
      have hA_cast : (A : ℝ) = (Q₁ : ℝ) * (2 : ℝ) ^ j := by dsimp only [A]; push_cast; rfl
      calc ∑ d ∈ Finset.Ioc A (2 * A), f d
          ≤ (A : ℝ)⁻¹ * ((x + 3 * ((2 * A : ℕ) : ℝ) ^ 2) * (Real.log x * chebyshevPsi x)) := by
            refine h1.trans ?_
            rw [hshift]
            exact mul_le_mul_of_nonneg_left hLS (inv_nonneg.mpr hAR_pos.le)
        _ ≤ (A : ℝ)⁻¹ * ((x + 3 * ((2 * A : ℕ) : ℝ) ^ 2) * (Real.log x * (6 * x))) := by
            gcongr
        _ = (6 * x * Real.log x) * (x / (A : ℝ) + 12 * (A : ℝ)) := by
            push_cast
            field_simp [hAR_pos.ne']
            ring
        _ = (6 * x * Real.log x) *
              (x / ((Q₁ : ℝ) * (2 : ℝ) ^ j) + 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j)) := by
            rw [hA_cast]
    have hsum_j1 : ∑ j ∈ Finset.range (J + 1), x / ((Q₁ : ℝ) * (2 : ℝ) ^ j) ≤ 2 * x / (Q₁ : ℝ) := by
      have hrw : ∑ j ∈ Finset.range (J + 1), x / ((Q₁ : ℝ) * (2 : ℝ) ^ j) =
          (x / (Q₁ : ℝ)) * ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrw]
      have h := mul_le_mul_of_nonneg_left (sum_inv_two_pow_le_two (J + 1)) (div_nonneg hx0.le hQ₁_pos.le)
      linarith [show x / (Q₁ : ℝ) * 2 = 2 * x / (Q₁ : ℝ) by ring]
    have hsum_j2 : ∑ j ∈ Finset.range (J + 1), 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j) ≤ 24 * (Q : ℝ) := by
      have hrw : ∑ j ∈ Finset.range (J + 1), 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j) =
          12 * (Q₁ : ℝ) * ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrw]
      have hpow : (Q₁ : ℝ) * (2 : ℝ) ^ J ≤ (Q : ℝ) := by exact_mod_cast hJ_le
      calc 12 * (Q₁ : ℝ) * ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j
          ≤ 12 * (Q₁ : ℝ) * (2 : ℝ) ^ (J + 1) :=
            mul_le_mul_of_nonneg_left (sum_two_pow_le (J + 1)) (by positivity)
        _ = 24 * ((Q₁ : ℝ) * (2 : ℝ) ^ J) := by rw [pow_succ]; ring
        _ ≤ 24 * (Q : ℝ) := by linarith
    calc ∑ d ∈ Finset.Ioc Q₁ Q, f d
        ≤ ∑ d ∈ (Finset.range (J + 1)).biUnion
            (fun j => Finset.Ioc (Q₁ * 2 ^ j) (Q₁ * 2 ^ (j + 1))), f d :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => hf_nn d
      _ ≤ ∑ j ∈ Finset.range (J + 1), ∑ d ∈ Finset.Ioc (Q₁ * 2 ^ j) (Q₁ * 2 ^ (j + 1)), f d :=
          sum_biUnion_le_of_nonneg_local _ _ f hf_nn
      _ ≤ ∑ j ∈ Finset.range (J + 1),
            (6 * x * Real.log x) *
              (x / ((Q₁ : ℝ) * (2 : ℝ) ^ j) + 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j)) :=
          Finset.sum_le_sum fun j _ => hblock j
      _ = (6 * x * Real.log x) *
            ((∑ j ∈ Finset.range (J + 1), x / ((Q₁ : ℝ) * (2 : ℝ) ^ j)) +
             (∑ j ∈ Finset.range (J + 1), 12 * ((Q₁ : ℝ) * (2 : ℝ) ^ j))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (6 * x * Real.log x) * (2 * x / (Q₁ : ℝ) + 24 * (Q : ℝ)) := by
          gcongr
      _ = 144 * x * (Q : ℝ) * Real.log x + 12 * x ^ 2 * Real.log x / (Q₁ : ℝ) := by ring

open Classical in
/-- **Unconditional Log-Weighted Dyadic Large-Sieve Primitive-Character Variance Bound**:
for ALL `1 ≤ Q₁ ≤ Q` and `x ≥ 4` with `(Q : ℝ) ≤ x`:
`∑ d ∈ Finset.Ioc Q₁ Q, (log (2 Q / d) / φ(d)) * ∑*_{χ mod d} ‖ψ(x, χ)‖² ≤ 288 * (x * Q * (log x) ^ 3 + x ^ 2 * (log x) ^ 3 / Q₁)`. -/
theorem prim_variance_Ioc_le {Q₁ Q : ℕ} (hQ₁ : 1 ≤ Q₁) (hQ : Q₁ ≤ Q)
    {x : ℝ} (hx : 4 ≤ x) (hQx : (Q : ℝ) ≤ x) :
    ∑ d ∈ Finset.Ioc Q₁ Q,
        (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
      288 * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hstep :
      ∑ d ∈ Finset.Ioc Q₁ Q,
          (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
        (2 * Real.log x) *
          ∑ d ∈ Finset.Ioc Q₁ Q,
            (d.totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := by have := (Finset.mem_Ioc.mp hd).1; omega
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hlog_le : Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ 2 * Real.log x := by
      have hQpos : (0 : ℝ) < (Q : ℝ) := by
        have : 1 ≤ Q := hQ₁.trans hQ
        exact_mod_cast this
      have hle : 2 * (Q : ℝ) / (d : ℝ) ≤ x ^ 2 := by
        calc 2 * (Q : ℝ) / (d : ℝ) ≤ 2 * (Q : ℝ) / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one hdR
          _ = 2 * (Q : ℝ) := div_one _
          _ ≤ 2 * x := by linarith
          _ ≤ x ^ 2 := by nlinarith
      calc Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ Real.log (x ^ 2) :=
            Real.log_le_log (by positivity) hle
        _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
    have hnn : 0 ≤ (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
        = Real.log (2 * (Q : ℝ) / (d : ℝ)) * ((d.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) := by ring
      _ ≤ (2 * Real.log x) * ((d.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hlog_le hnn
  have hunw := prim_variance_Ioc_unweighted_le hQ₁ hQ hx
  have hL2_le_L3 : (Real.log x) ^ 2 ≤ (Real.log x) ^ 3 := by nlinarith
  have hQ₁_pos : (0 : ℝ) < (Q₁ : ℝ) := Nat.cast_pos.mpr hQ₁
  calc ∑ d ∈ Finset.Ioc Q₁ Q,
          (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
      ≤ (2 * Real.log x) * (144 * x * (Q : ℝ) * Real.log x + 12 * x ^ 2 * Real.log x / (Q₁ : ℝ)) :=
        hstep.trans (mul_le_mul_of_nonneg_left hunw (by linarith))
    _ = 288 * x * (Q : ℝ) * (Real.log x) ^ 2 + 24 * x ^ 2 * (Real.log x) ^ 2 / (Q₁ : ℝ) := by ring
    _ ≤ 288 * x * (Q : ℝ) * (Real.log x) ^ 3 + 288 * x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ) := by
        have h1 : 288 * x * (Q : ℝ) * (Real.log x) ^ 2 ≤ 288 * x * (Q : ℝ) * (Real.log x) ^ 3 :=
          mul_le_mul_of_nonneg_left hL2_le_L3 (by positivity)
        have h2 : 24 * x ^ 2 * (Real.log x) ^ 2 / (Q₁ : ℝ) ≤ 288 * x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hQ₁_pos.le
          have : 24 * (Real.log x) ^ 2 ≤ 288 * (Real.log x) ^ 3 := by nlinarith
          nlinarith [sq_nonneg x]
        linarith
    _ = 288 * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)) := by ring

/-- Single-modulus arithmetic-progression mean-square variance
`∑_{a < q, (a, q) = 1} (ψ(x; q, a) - x / φ(q))²`. -/
def psiAPVariance (q : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)) ^ 2

theorem psiAPVariance_nonneg (q : ℕ) (x : ℝ) : 0 ≤ psiAPVariance q x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Exact identification of `psiAPVariance q x` with the sum over `(ZMod q)ˣ` for every `q ≥ 1`. -/
theorem psiAPVariance_eq_units {q : ℕ} [NeZero q] (x : ℝ) :
    psiAPVariance q x =
      ∑ a : (ZMod q)ˣ,
        (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ)) ^ 2 := by
  unfold psiAPVariance
  symm
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
  · intro _ _; rfl

open Classical in
/-- **Exact Variance-to-Primitive-Characters Transfer on `Finset.Icc 1 Q`**:
for EVERY `Q ≥ 1` and `x ≥ 4` with `(Q : ℝ) ≤ x`,
the full AP mean-square variance `∑_{q ≤ Q} ∑_{(a,q)=1} (ψ(x; q, a) - x / φ(q))²` is bounded by
the principal error, the divisor-weighted primitive character sum over `2 ≤ d ≤ Q`, and the
`O(x Q (log x)³)` induction error! -/
theorem ap_variance_Icc_le_principal_add_prim_sum {Q : ℕ} (hQ : 1 ≤ Q)
    {x : ℝ} (hx : 4 ≤ x) (hQx : (Q : ℝ) ≤ x) :
    ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤
      48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x +
      24 * ∑ d ∈ Finset.Icc 2 Q,
        (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 +
      200 * x * (Q : ℝ) * (Real.log x) ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log x := by
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
    have hle : 2 * (Q : ℝ) ≤ x ^ 2 := by nlinarith
    calc Real.log (2 * (Q : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hlog_le_x : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  -- Per-modulus bound via `(u + v)^2 ≤ 2 u^2 + 2 v^2` and `psiAP_variance_eq_nonprincipal_chars`
  have hper_q : ∀ q ∈ Finset.Icc 1 Q,
      psiAPVariance q x ≤
        4 * (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4) +
        4 * (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2 +
        4 * (Real.log x) ^ 4 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have : NeZero q := ⟨by omega⟩
    rw [psiAPVariance_eq_units]
    have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1)
    have hsplit_a :
        ∑ a : (ZMod q)ˣ,
            (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ)) ^ 2 ≤
          2 * ∑ a : (ZMod q)ˣ,
              (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
                Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)) ^ 2 +
          2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 / (q.totient : ℝ)) := by
      have hterm : ∀ a : (ZMod q)ˣ,
          (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ)) ^ 2 ≤
            2 * (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
                  Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)) ^ 2 +
            2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) / (q.totient : ℝ)) ^ 2 := by
        intro a
        set u := Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
          Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)
        set v := (Stage2DirichletAP.chebyshevPsiCoprime q x - x) / (q.totient : ℝ)
        have heq : Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ) = u + v := by
          dsimp only [u, v]; ring
        rw [heq]
        nlinarith [sq_nonneg (u - v)]
      calc ∑ a : (ZMod q)ˣ,
              (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ)) ^ 2
          ≤ ∑ a : (ZMod q)ˣ,
              (2 * (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
                    Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)) ^ 2 +
               2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) / (q.totient : ℝ)) ^ 2) :=
            Finset.sum_le_sum fun a _ => hterm a
        _ = 2 * ∑ a : (ZMod q)ˣ,
                (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
                  Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)) ^ 2 +
            2 * ((q.totient : ℝ) * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) / (q.totient : ℝ)) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              ZMod.card_units_eq_totient, nsmul_eq_mul]; ring
        _ = 2 * ∑ a : (ZMod q)ˣ,
                (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x -
                  Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ)) ^ 2 +
            2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 / (q.totient : ℝ)) := by
            congr 1; field_simp [hphi_pos.ne']
    -- Bound principal part `(ψ_coprime(x; q) - x)^2 ≤ 2 |ψ(x) - x|^2 + 8 (log x)^4`
    have hprinc : (Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 ≤
        2 * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4) := by
      have hcop_bd := Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_le_log hq1 hx1
      have hcop_nn := (Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_bounds hq1 hx1).1
      have hlogq : Real.log (q : ℝ) ≤ Real.log x :=
        Real.log_le_log (Nat.cast_pos.mpr hq1) ((by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQx)
      have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hdiff_le : RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x ≤
          2 * (Real.log x) ^ 2 := by
        have h1 : Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log x := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]
          nlinarith
        calc RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x
            ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := hcop_bd
          _ ≤ (2 * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right h1 (by linarith)
          _ = 2 * (Real.log x) ^ 2 := by ring
      have hdiff_sq : (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) ^ 2 ≤
          4 * (Real.log x) ^ 4 := by
        have := pow_le_pow_left₀ hcop_nn hdiff_le 2
        linarith [show (2 * (Real.log x) ^ 2) ^ 2 = 4 * (Real.log x) ^ 4 by ring]
      set u := RHDirect.chebyshevPsi x - x
      set v := RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x
      have heq : Stage2DirichletAP.chebyshevPsiCoprime q x - x = u - v := by dsimp only [u, v]; ring
      rw [heq, sq_abs]
      nlinarith [sq_nonneg (u + v)]
    -- Transfer non-principal character sum to primitive characters dividing `q`
    rw [Stage3BombieriVinogradov.psiAP_variance_eq_nonprincipal_chars] at hsplit_a
    have hnonprinc :
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
          2 * (∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2) +
          2 * (q.totient : ℝ) * (Real.log x) ^ 4 := by
      have h1 :
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (2 * ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ^ 2 +
                2 * (Real.log x) ^ 4) := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        have htr := norm_chebyshevPsiChar_sub_primitive_le hχne hx1
        have hlogq : Real.log (q : ℝ) ≤ Real.log x :=
          Real.log_le_log (Nat.cast_pos.mpr hq1) ((by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQx)
        have hdiff : ‖Stage2DirichletAP.chebyshevPsiChar χ x -
            Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤ (Real.log x) ^ 2 := by
          calc _ ≤ Real.log (q : ℝ) * Real.log x := htr
            _ ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_right hlogq (by linarith)
            _ = (Real.log x) ^ 2 := by ring
        have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
            ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ +
              ‖Stage2DirichletAP.chebyshevPsiChar χ x -
                Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ := by
          simpa using norm_add_le (Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
            (Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
        have hsq1 : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
            2 * ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ^ 2 +
              2 * ‖Stage2DirichletAP.chebyshevPsiChar χ x -
                Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg _) htri 2
          nlinarith [sq_nonneg (‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ -
            ‖Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖)]
        have hsq2 : ‖Stage2DirichletAP.chebyshevPsiChar χ x -
            Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ^ 2 ≤ (Real.log x) ^ 4 := by
          have := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
          linarith [show ((Real.log x) ^ 2) ^ 2 = (Real.log x) ^ 4 by ring]
        linarith
      -- Re-index `χ ↦ ⟨χ.conductor, χ.primitiveCharacter⟩` injectively into the sigma finset
      set target : Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
        ((Finset.Icc 2 Q).filter (fun d => d ∣ q)).sigma fun d =>
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
        have hd3 : 3 ≤ χ.conductor := three_le_conductor_of_ne_one hχne
        have hdq : χ.conductor ∣ q := χ.conductor_dvd_level
        have hdle : χ.conductor ≤ Q := (Nat.le_of_dvd hq1 hdq).trans hqQ
        simp only [target, toPrim, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_univ, true_and]
        exact ⟨⟨⟨by omega, hdle⟩, hdq⟩, χ.primitiveCharacter_isPrimitive⟩
      have hprim_sum :
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ^ 2 ≤
            ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2 := by
        have hsig :
            ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ ^ 2 =
              ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
                ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2 :=
          Finset.sum_sigma _ _ _
        rw [← hsig]
        calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (toPrim χ).2 x‖ ^ 2
            = ∑ p ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).image toPrim,
                ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ ^ 2 :=
              (Finset.sum_image (f := fun p : Σ d : ℕ, DirichletCharacter ℂ d =>
                ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ ^ 2) hinj).symm
          _ ≤ ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
                fun _ _ _ => sq_nonneg _
      have hcard_le : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
        have htot : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        have hnat : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
          calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
              ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card (Finset.erase_subset _ _)
            _ = q.totient := by rw [Finset.card_univ, htot]
        exact_mod_cast hnat
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
      have herr_le : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * (2 * (Real.log x) ^ 4) ≤
          2 * (q.totient : ℝ) * (Real.log x) ^ 4 := by
        have := mul_le_mul_of_nonneg_right hcard_le (show 0 ≤ 2 * (Real.log x) ^ 4 by positivity)
        linarith
      linarith
    have hcomb1 : 2 * ((q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2) ≤
        4 * (q.totient : ℝ)⁻¹ *
          (∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2) +
        4 * (Real.log x) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hnonprinc (show 0 ≤ 2 * (q.totient : ℝ)⁻¹ by positivity)
      have hcancel : 2 * (q.totient : ℝ)⁻¹ * (2 * (q.totient : ℝ) * (Real.log x) ^ 4) = 4 * (Real.log x) ^ 4 := by
        field_simp [hphi_pos.ne']; ring
      linarith
    have hcomb2 : 2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 / (q.totient : ℝ)) ≤
        4 * (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4) := by
      have h := mul_le_mul_of_nonneg_left hprinc (show 0 ≤ 2 * (q.totient : ℝ)⁻¹ by positivity)
      have hrw : 2 * ((Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 / (q.totient : ℝ)) =
          2 * (q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x) ^ 2 := by ring
      linarith
    linarith
  -- Sum `hper_q` over `q ∈ Finset.Icc 1 Q` and swap the divisor sum!
  have hsum_all := Finset.sum_le_sum hper_q
  simp only [Finset.sum_add_distrib] at hsum_all
  -- Term 1: `∑_{q ≤ Q} 4 φ(q)⁻¹ (|ψ(x) - x|² + 4 (log x)⁴)`
  have hT1 :
      ∑ q ∈ Finset.Icc 1 Q,
          4 * (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4) ≤
        48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x + 192 * x * (Q : ℝ) * (Real.log x) ^ 3 := by
    have hfac :
        ∑ q ∈ Finset.Icc 1 Q,
            4 * (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4) =
          (4 * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4)) *
            ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [hfac]
    have hinv := (sum_inv_totient_le_log hQ).trans (by linarith : 6 * Real.log (2 * (Q : ℝ)) ≤ 12 * Real.log x)
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hlog5 : (Real.log x) ^ 5 ≤ x * (Q : ℝ) * (Real.log x) ^ 3 := by
      have hlog2_le : (Real.log x) ^ 2 ≤ x := by
        have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
        have hsq : Real.log x ≤ 2 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]; linarith
        -- Actually even simpler: for `x ≥ 4`, `(log x)^2 ≤ x` via `Real.log x ≤ x ^ (1/2) / (1/2)`?
        -- Wait: `(2 √x)^2 = 4 x`, so let's use `(log x)^2 ≤ 4 x`! Wait: check `192`:
        -- `192 / 4 = 48`! Let's bound `192 * (log x)^5` directly via `Real.log_le_rpow_div` with `1/4` or `1/2`?
        -- Wait: `log x ≤ √x` IS true for ALL `x > 0`? Check `x = e^2 ≈ 7.39`: `log(e^2) = 2 < e = 2.718`!
        -- Proof: `log(√x) = (log x)/2 ≤ √x - 1 < √x`? That gives `log x ≤ 2 √x`, wait:
        -- `(log x) / 2 = log (√x)`, no, `(log x) / 2 ≤ √x - 1` gives `log x ≤ 2 √x - 2`.
        -- Better: for `u = √x ≥ 2`, `log x = 2 log u`. Is `2 log u ≤ u` for `u ≥ 2`?
        -- `2 log u ≤ u ↔ log u ≤ u / 2 ↔ u ≤ e^{u/2}`, and `1 + u/2 + (u/2)^2/2 > u` for `u ≥ 2`!
        -- Wait: `e^{u/2} ≥ 1 + u/2 + (u/2)^2 / 2`! Even simpler: `e^t ≥ 1 + t + t^2 / 2`!
        have hu_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
        have hu_ge2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith : (2 : ℝ) ^ 2 ≤ x)
        have hexp_t : Real.sqrt x ≤ Real.exp (Real.sqrt x / 2) := by
          have h := Real.sum_le_exp_of_nonneg (show 0 ≤ Real.sqrt x / 2 by positivity) 3
          simp [Finset.sum_range_succ, Nat.factorial] at h
          nlinarith
        have hlog_u : Real.log (Real.sqrt x) ≤ Real.sqrt x / 2 :=
          (Real.log_le_log hu_pos hexp_t).trans_eq (Real.log_exp _)
        rw [Real.log_sqrt hx0.le] at hlog_u
        have hlog_le_sqrt : Real.log x ≤ Real.sqrt x := by linarith
        have hsq := pow_le_pow_left₀ (by linarith) hlog_le_sqrt 2
        rwa [Real.sq_sqrt hx0.le] at hsq
      calc (Real.log x) ^ 5 = (Real.log x) ^ 2 * (Real.log x) ^ 3 := by ring
        _ ≤ x * (Real.log x) ^ 3 := mul_le_mul_of_nonneg_right hlog2_le (by positivity)
        _ ≤ x * (Q : ℝ) * (Real.log x) ^ 3 := by
            have hxQ : x ≤ x * (Q : ℝ) := by nlinarith
            exact mul_le_mul_of_nonneg_right hxQ (pow_nonneg (by linarith : 0 ≤ Real.log x) 3)
    calc (4 * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4)) *
            ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹
        ≤ (4 * (|RHDirect.chebyshevPsi x - x| ^ 2 + 4 * (Real.log x) ^ 4)) * (12 * Real.log x) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x + 192 * (Real.log x) ^ 5 := by ring
      _ ≤ 48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x + 192 * x * (Q : ℝ) * (Real.log x) ^ 3 := by
          linarith
  -- Term 2: swap sum over `q` and `d` and apply `sum_inv_totient_dvd_le`
  have hT2 :
      ∑ q ∈ Finset.Icc 1 Q,
          4 * (q.totient : ℝ)⁻¹ *
            ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2 ≤
        24 * ∑ d ∈ Finset.Icc 2 Q,
          (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2 := by
    set g : ℕ → ℝ := fun d =>
      ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
        ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ^ 2
    have hg_nn : ∀ d, 0 ≤ g d := fun d => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hswap :
        ∑ q ∈ Finset.Icc 1 Q,
            4 * (q.totient : ℝ)⁻¹ * ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q), g d =
          4 * ∑ d ∈ Finset.Icc 2 Q,
            (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) * g d := by
      have h1 : ∀ q ∈ Finset.Icc 1 Q,
          4 * (q.totient : ℝ)⁻¹ * ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ∣ q), g d =
            4 * ∑ d ∈ Finset.Icc 2 Q, if d ∣ q then (q.totient : ℝ)⁻¹ * g d else 0 := by
        intro q _
        rw [Finset.sum_filter, mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by split_ifs <;> ring
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
    have hdQ : d ≤ Q := (Finset.mem_Icc.mp hd).2
    have hdvd := sum_inv_totient_dvd_le hd1 hdQ
    have hmul := mul_le_mul_of_nonneg_right hdvd (hg_nn d)
    have h4 := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
    linarith [show 4 * ((6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) * g d) =
      24 * ((Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) * g d) by ring]
  -- Term 3: `∑_{q ∈ Icc 1 Q} 4 (log x)⁴ = 4 Q (log x)⁴ ≤ 4 x Q (log x)³`
  have hT3 : ∑ _q ∈ Finset.Icc 1 Q, 4 * (Real.log x) ^ 4 ≤ 4 * x * (Q : ℝ) * (Real.log x) ^ 3 := by
    rw [Finset.sum_const, Nat.card_Icc, show Q + 1 - 1 = Q by omega, nsmul_eq_mul]
    have h1 : (Real.log x) ^ 4 ≤ x * (Real.log x) ^ 3 := by
      calc (Real.log x) ^ 4 = Real.log x * (Real.log x) ^ 3 := by ring
        _ ≤ x * (Real.log x) ^ 3 := mul_le_mul_of_nonneg_right hlog_le_x (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * (Q : ℝ) by positivity)
    linarith
  have hpos_extra : 0 ≤ 4 * x * (Q : ℝ) * (Real.log x) ^ 3 := by positivity
  linarith

/-! ## Section 2: Uniform Real-Character Zero-Free Region & Unconditional Siegel's Theorem -/

/-- **Unconditional 3-4-1 Positivity for Real Characters with `ζ(σ + 2 i t)` Directly**:
for every `q ≥ 1`, real `χ : DirichletCharacter ℂ q`, `σ > 1`, and `t ∈ ℝ`,
`0 ≤ 3 * (-ζ'/ζ)(σ).re + 4 * (-L'/L)(χ, σ + i t).re + (-ζ'/ζ)(σ + 2 i t).re`. -/
theorem three_four_one_real_char_zeta_re_nonneg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re +
        4 * (Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
        (Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simpa using hσ
  rw [Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs0,
    Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs1,
    Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs2]
  have hS0 : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs0
  have hS1 : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs1
  have hS2 : LSeriesSummable (fun n => (Λ n : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs2
  have hR0 : Summable (fun n => (3 : ℝ) * (LSeries.term (fun k => (Λ k : ℂ)) (σ : ℂ) n).re) :=
    (Complex.reCLM.summable hS0).mul_left 3
  have hR1 : Summable (fun n => (4 : ℝ) * (LSeries.term (fun k => χ k * (Λ k : ℂ)) ((σ : ℂ) + I * (t : ℂ)) n).re) :=
    (Complex.reCLM.summable hS1).mul_left 4
  have hR2 : Summable (fun n => (LSeries.term (fun k => (Λ k : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) n).re) :=
    Complex.reCLM.summable hS2
  unfold LSeries
  rw [Complex.re_tsum hS0, Complex.re_tsum hS1, Complex.re_tsum hS2,
    ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add hR0 hR1, ← Summable.tsum_add (hR0.add hR1) hR2]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term_of_ne_zero hn.ne']
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hpow_σ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    have hpow_1 : (n : ℂ) ^ ((σ : ℂ) + I * (t : ℂ)) =
        (((n : ℝ) ^ σ : ℝ) : ℂ) * (n : ℂ) ^ (I * (t : ℂ)) := by
      rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne'), hpow_σ]
    have hpow_2 : (n : ℂ) ^ ((σ : ℂ) + 2 * I * (t : ℂ)) =
        (((n : ℝ) ^ σ : ℝ) : ℂ) * (n : ℂ) ^ (2 * I * (t : ℂ)) := by
      rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne'), hpow_σ]
    set w : ℂ := (n : ℂ) ^ (-(I * (t : ℂ)))
    have hw_norm : ‖w‖ = 1 := by
      dsimp only [w]
      rw [Complex.norm_natCast_cpow_of_pos hn]
      simp
    have hw_inv : ((n : ℂ) ^ (I * (t : ℂ)))⁻¹ = w := by
      dsimp only [w]; rw [Complex.cpow_neg]
    have hw_sq : ((n : ℂ) ^ (2 * I * (t : ℂ)))⁻¹ = w ^ 2 := by
      rw [← hw_inv, sq, ← mul_inv, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne')]
      congr 2; ring
    have hterm0 : ((Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ)).re = Λ n / (n : ℝ) ^ σ := by
      rw [hpow_σ, ← Complex.ofReal_div, Complex.ofReal_re]
    have hterm1 : (χ (n : ZMod q) * (Λ n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + I * (t : ℂ))).re =
        (Λ n / (n : ℝ) ^ σ) * (χ (n : ZMod q) * w).re := by
      rw [hpow_1, div_mul_eq_div_div, div_eq_mul_inv _ ((n : ℂ) ^ (I * (t : ℂ))), hw_inv]
      have hrearr : χ (n : ZMod q) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) * w =
          (((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)) * (χ (n : ZMod q) * w) := by
        push_cast; ring
      rw [hrearr, Complex.re_ofReal_mul]
    have hterm2 : ((Λ n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 2 * I * (t : ℂ))).re =
        (Λ n / (n : ℝ) ^ σ) * (w ^ 2).re := by
      rw [hpow_2, div_mul_eq_div_div, div_eq_mul_inv _ ((n : ℂ) ^ (2 * I * (t : ℂ))), hw_sq]
      have hrearr : (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) * w ^ 2 =
          (((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)) * (w ^ 2) := by
        push_cast; ring
      rw [hrearr, Complex.re_ofReal_mul]
    rw [hterm0, hterm1, hterm2]
    have hfac :
        3 * (Λ n / (n : ℝ) ^ σ) + 4 * (Λ n / (n : ℝ) ^ σ * (χ (n : ZMod q) * w).re) +
            Λ n / (n : ℝ) ^ σ * (w ^ 2).re =
          (Λ n / (n : ℝ) ^ σ) * (3 + 4 * (χ (n : ZMod q) * w).re + (w ^ 2).re) := by ring
    rw [hfac]
    refine mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ)) ?_
    rcases Stage7SiegelWalfisz.real_char_apply_trichotomy hreal (n : ZMod q) with h0 | h1 | hm1
    · rw [h0, zero_mul, Complex.zero_re, mul_zero, add_zero]
      have hle1 : |(w ^ 2).re| ≤ 1 := by
        calc |(w ^ 2).re| ≤ ‖w ^ 2‖ := Complex.abs_re_le_norm _
          _ = ‖w‖ ^ 2 := norm_pow _ _
          _ = 1 := by rw [hw_norm]; norm_num
      linarith [(abs_le.mp hle1).1]
    · rw [h1, one_mul]
      exact Stage3ZeroFreeRegion.three_four_one_complex_nonneg hw_norm.le
    · rw [hm1]
      have hneg : (-1 : ℂ) * w = -w := by ring
      rw [hneg]
      have hsq : (-w) ^ 2 = w ^ 2 := by ring
      rw [← hsq]
      exact Stage3ZeroFreeRegion.three_four_one_complex_nonneg (by rw [norm_neg]; exact hw_norm.le)

/-- Conjugate symmetry of `LFunction χ` on `Re(s) > 0` for every real non-principal character `χ`. -/
theorem LFunction_conj_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.LFunction χ s) := by
  have hs_conj : 0 < (starRingEnd ℂ s).re := by simpa using hs
  rw [Stage5DirichletLZeroFree.LFunction_eq_mul_mellin_of_ne_one hχ hs,
    Stage5DirichletLZeroFree.LFunction_eq_mul_mellin_of_ne_one hχ hs_conj,
    map_mul, ← integral_conj]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  rw [map_mul]
  congr 1
  · unfold Stage3RealAnalyticLandau.stepSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact (Complex.conj_eq_iff_im.mpr (hreal (n : ZMod q))).symm
  · have hcpow : starRingEnd ℂ ((t : ℂ) ^ (-s - 1)) = (t : ℂ) ^ (-(starRingEnd ℂ s) - 1) := by
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      rw [Complex.cpow_def_of_ne_zero htC, Complex.cpow_def_of_ne_zero htC,
        ← Complex.exp_conj, map_mul, map_sub, map_neg, map_one, ← Complex.ofReal_log ht0.le,
        Complex.conj_ofReal]
    exact hcpow.symm

/-- **UNCONDITIONAL UNIFORM NON-REAL LOW-HEIGHT ZERO-FREE REGION FOR REAL CHARACTERS**:
`∃ c > 0`, for EVERY `q ≥ 1` (`[NeZero q]`), EVERY real non-principal `χ : DirichletCharacter ℂ q`,
and EVERY `s : ℂ` with `s.im ≠ 0` and `|s.im| ≤ 1`:
`1 - c / Real.log (2 * q) ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0`. -/
theorem LFunction_real_char_zeroFree_low_nonreal :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ s : ℂ, s.im ≠ 0 → |s.im| ≤ 1 →
          1 - c / Real.log (2 * (q : ℝ)) ≤ s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hzf_zeta⟩ := Stage6EffectivePNT.negLogDerivZeta_zeroFree_bound
  obtain ⟨c₂, hc₂, C₂, hC₂, _, hnear_zeta⟩ := Stage6EffectivePNT.negLogDerivZeta_sub_pole_bounded_near_one
  set K₀ : ℝ := max 100000 (40 * (C₂ + C₁ * (Real.log 4) ^ 2 + 1000)) with hK₀_def
  have hK₀_ge : 100000 ≤ K₀ := le_max_left _ _
  have hK₀_pos : 0 < K₀ := by linarith
  have hK₀_bd : 40 * (C₂ + C₁ * (Real.log 4) ^ 2 + 1000) ≤ K₀ := le_max_right _ _
  set c : ℝ := 1 / (4 * K₀) with hc_def
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun q _ χ hχ hreal s htim htle hs_re hzero => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  set L : ℝ := Real.log (2 * (q : ℝ)) with hL_def
  have hL_gt : (1.38 : ℝ) < L := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hlog4 : (1.38 : ℝ) < Real.log 4 := by linarith [Real.log_two_gt_d9]
    exact lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL_pos : 0 < L := by linarith
  have hL_ge1 : 1 ≤ L := by linarith
  have hre_lt1 : s.re < 1 := by
    by_contra hge; push Not at hge
    exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (.inl hχ) hge hzero
  set β : ℝ := s.re
  set t : ℝ := s.im
  set η : ℝ := 1 / (K₀ * L) with hη_def
  have hη_pos : 0 < η := by positivity
  have hη_small : η ≤ 1 / 100000 := by
    dsimp only [η]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1β_le : 1 - β ≤ η / 4 := by
    have : c / L = η / 4 := by dsimp only [c, η]; field_simp [hK₀_pos.ne', hL_pos.ne']
    linarith
  have hL_le_2q : L ≤ 2 * (q : ℝ) := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlog10000 : Real.log (10000 : ℝ) < 10 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 10000) (by norm_num : (10000 : ℝ) ≤ 2 ^ 14)
    rw [Real.log_pow] at h1; norm_num at h1
    linarith [Real.log_two_lt_d9]
  -- Helper: Landau setup for `LFunction χ` at any `s₀ = (1 + δ) + I * y` with `0 < δ ≤ 1/4`, `|y| ≤ 1`
  have hlandau_setup : ∀ (δ y : ℝ), 0 < δ → δ ≤ 1 / 4 → |y| ≤ 1 →
      let s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + I * (y : ℂ)
      let M : ℝ := 16 * (q : ℝ) / δ
      1 ≤ M ∧
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s₀ (1 / 2)) ∧
      DirichletCharacter.LFunction χ s₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall s₀ (1 / 2),
        ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ s₀‖) ∧
      (∀ ρ ∈ Metric.closedBall s₀ (1 / 4),
        DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ s₀.re) := by
    intro δ y hδ0 hδ4 hy1 s₀ M
    have hM1 : 1 ≤ M := by dsimp only [M]; rw [le_div_iff₀ hδ0]; linarith
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s₀ (1 / 2)) :=
      (DifferentiableOn.analyticOnNhd
        (fun z _ => (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ)).differentiableWithinAt)
        isOpen_univ).mono (Set.subset_univ _)
    have hs₀_re : s₀.re = 1 + δ := by simp [s₀]
    have hs₀_im : s₀.im = y := by simp [s₀]
    have hnz : DirichletCharacter.LFunction χ s₀ ≠ 0 :=
      Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (.inl hχ) (by rw [hs₀_re]; linarith)
    have hbd : ∀ z ∈ Metric.closedBall s₀ (1 / 2),
        ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ s₀‖ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im : |z.im| ≤ 3 / 2 := by
        have htri : |z.im| ≤ |y| + |z.im - y| := by simpa [add_sub_cancel] using abs_add_le y (z.im - y)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 8 * (q : ℝ) := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ (q : ℝ) * (2 + 3 / 2) / (1 / 2) :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hq_pos.le)
                (by norm_num) (by linarith)
          _ ≤ 8 * (q : ℝ) := by linarith
      have hinv : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 2 / δ := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + δ) y).2.1
        have hsub : (1 + δ) - 1 = δ := by ring
        rw [hsub] at h
        exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ0.le)
      have hratio : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ s₀‖ ≤ M := by
        rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
          norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (8 * (q : ℝ)) * (2 / δ) := mul_le_mul hz_bd hinv (norm_nonneg _) (by positivity)
          _ = M := by dsimp only [M]; ring
      exact (div_le_iff₀ (norm_pos_iff.mpr hnz)).mp hratio
    have hzeros : ∀ ρ ∈ Metric.closedBall s₀ (1 / 4),
        DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ s₀.re := by
      intro ρ _ hρ0
      by_contra hgt; push Not at hgt
      exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (.inl hχ)
        (by rw [hs₀_re] at hgt; linarith) hρ0
    exact ⟨hM1, han, hnz, hbd, hzeros⟩
  by_cases hhigh : 2 * η ≤ |t|
  · -- Subcase A: `2 * η ≤ |t| ≤ 1`, apply 3-4-1 inequality at `σ = 1 + η`!
    set σ : ℝ := 1 + η
    have hσ1 : 1 < σ := by dsimp only [σ]; linarith
    have hpos := three_four_one_real_char_zeta_re_nonneg hreal hσ1 t
    have hZ0 : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / η + 1 := by
      have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ1
      have hsub : σ - 1 = η := by dsimp only [σ]; ring
      rwa [hsub] at h
    have hZ2 : (Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + 2 * I * (t : ℂ))).re ≤
        1 / (16 * η) + C₂ + C₁ * (Real.log 4) ^ 2 := by
      set z₂ : ℂ := (σ : ℂ) + 2 * I * (t : ℂ)
      have hz₂_re : z₂.re = 1 + η := by simp [z₂, σ]
      have hz₂_im : z₂.im = 2 * t := by simp [z₂]
      by_cases ht_half : |t| ≤ 1 / 2
      · have hne1 : z₂ ≠ 1 := by
          intro h1
          have := congrArg Complex.re h1
          rw [hz₂_re, Complex.one_re] at this; linarith
        have hnear := hnear_zeta z₂ (by rw [hz₂_re]; linarith) (by rw [hz₂_re]; linarith)
          (by rw [hz₂_im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith) hne1
        have hre_diff :
            (Stage3ZeroFreeRegion.negLogDerivZeta z₂).re - (1 / (z₂ - 1)).re ≤ C₂ := by
          unfold Stage3ZeroFreeRegion.negLogDerivZeta
          rw [← Complex.sub_re]
          exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hnear
        have hpole_re : (1 / (z₂ - 1)).re = η / (η ^ 2 + 4 * t ^ 2) := by
          have hsub : z₂ - 1 = (η : ℂ) + ((2 * t : ℝ) : ℂ) * I :=
            Complex.ext (by simp [z₂, σ]) (by simp [z₂])
          rw [hsub, one_div, Complex.inv_re, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, zero_add,
            Complex.mul_im]
          ring
        have hpole_le : η / (η ^ 2 + 4 * t ^ 2) ≤ 1 / (16 * η) := by
          have ht2 : 4 * η ^ 2 ≤ t ^ 2 := by
            have := pow_le_pow_left₀ (by positivity) hhigh 2
            rw [sq_abs] at this; linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hC1_nn : 0 ≤ C₁ * (Real.log 4) ^ 2 := by positivity
        linarith
      · push Not at ht_half
        have h1_le : 1 ≤ |z₂.im| := by
          rw [hz₂_im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have hbd := hzf_zeta z₂ (by rw [hz₂_re]; linarith [div_pos hc₁ (Real.log_pos (by linarith [abs_nonneg z₂.im] : (1 : ℝ) < |z₂.im| + 2))])
          (by rw [hz₂_re]; linarith) h1_le
        have hlog4_ge : Real.log (|z₂.im| + 2) ≤ Real.log 4 := by
          have : |z₂.im| ≤ 2 := by
            rw [hz₂_im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
          exact Real.log_le_log (by linarith [abs_nonneg z₂.im]) (by linarith)
        have hsq : (Real.log (|z₂.im| + 2)) ^ 2 ≤ (Real.log 4) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith [abs_nonneg z₂.im])) hlog4_ge 2
        have hre_le : (Stage3ZeroFreeRegion.negLogDerivZeta z₂).re ≤ C₁ * (Real.log 4) ^ 2 := by
          unfold Stage3ZeroFreeRegion.negLogDerivZeta
          calc (-deriv riemannZeta z₂ / riemannZeta z₂).re
              ≤ ‖-deriv riemannZeta z₂ / riemannZeta z₂‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
            _ ≤ C₁ * (Real.log (|z₂.im| + 2)) ^ 2 := hbd
            _ ≤ C₁ * (Real.log 4) ^ 2 := mul_le_mul_of_nonneg_left hsq hC₁.le
        have hnn : 0 ≤ 1 / (16 * η) + C₂ := by positivity
        linarith
    -- Landau bound for `LFunction χ` at `s₀ = σ + I * t`
    obtain ⟨hM1, han, hnz, hbd, hzeros⟩ := hlandau_setup η t hη_pos (by linarith) htle
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ)
    set M : ℝ := 16 * (q : ℝ) / η
    have hs_mem : s ∈ Metric.closedBall s₀ (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : s - s₀ = (((β - (1 + η) : ℝ) : ℂ)) := Complex.ext (by simp [s₀, β]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hlandau := Stage5ZetaZeroFree.landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM1 han hnz hbd hzeros hs_mem hzero
    have hinv_re : (1 / (s₀ - s)).re = 1 / (1 + η - β) := by
      have hdiff : s₀ - s = (((1 + η - β : ℝ) : ℂ)) := Complex.ext (by simp [s₀, β]) (by simp [s₀, t])
      rw [hdiff, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    have herr_s : (s₀ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
      have : (s₀ - s).re = 1 + η - β := by simp [s₀, β]
      rw [this]; norm_num; linarith
    have h1_div : 4 / (5 * η) ≤ 1 / (1 + η - β) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      linarith
    have hLχ : 4 * (Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re ≤
        32 * Real.log M + 4 - 16 / (5 * η) := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
      have hs₀_eq : ((σ : ℂ) + I * (t : ℂ)) = s₀ := rfl
      rw [hs₀_eq]
      rw [hinv_re, h8] at hlandau
      linarith [show 4 * (4 / (5 * η)) = 16 / (5 * η) by ring]
    have hlogM : Real.log M ≤ 16 * K₀ / 10000 + 10 + 2 * L := by
      have hMeq : M = (16 * K₀ / 10000) * 10000 * ((q : ℝ) * L) := by
        dsimp only [M, η]; field_simp [hK₀_pos.ne', hL_pos.ne']
      have hqL : (q : ℝ) * L ≤ (2 * (q : ℝ)) ^ 2 := by nlinarith
      have hMle : M ≤ (16 * K₀ / 10000) * 10000 * (2 * (q : ℝ)) ^ 2 := by rw [hMeq]; gcongr
      calc Real.log M ≤ Real.log ((16 * K₀ / 10000) * 10000 * (2 * (q : ℝ)) ^ 2) :=
            Real.log_le_log (by positivity) hMle
        _ = Real.log (16 * K₀ / 10000) + Real.log 10000 + Real.log ((2 * (q : ℝ)) ^ 2) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num)]
        _ = Real.log (16 * K₀ / 10000) + Real.log 10000 + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 16 * K₀ / 10000 + 10 + 2 * L := by
            have := (Real.log_le_sub_one_of_pos (show 0 < 16 * K₀ / 10000 by positivity))
            linarith
    have hcomb : (11 / 80 : ℝ) * (K₀ * L) ≤
        7 + C₂ + C₁ * (Real.log 4) ^ 2 + 32 * (16 * K₀ / 10000 + 10 + 2 * L) := by
      have hinvη : 1 / η = K₀ * L := by dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
      have h16 : 1 / (16 * η) = (1 / 16) * (K₀ * L) := by dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
      have h5 : 16 / (5 * η) = (16 / 5) * (K₀ * L) := by dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
      linarith
    have hK₀L_ge : K₀ ≤ K₀ * L := by nlinarith
    have hL_le_K₀L : 64 * L ≤ (1 / 1000 : ℝ) * (K₀ * L) := by nlinarith
    nlinarith
  · -- Subcase B: `0 < |t| < 2 * η`, apply 2-character positivity at `σ₀ = 1 + 4 * η` with conjugate zeros `{s, conj s}`!
    push Not at hhigh
    set δ : ℝ := 4 * η
    have hδ0 : 0 < δ := by positivity
    have hδ4 : δ ≤ 1 / 4 := by dsimp only [δ]; linarith
    set σ₀ : ℝ := 1 + δ
    have hσ₀1 : 1 < σ₀ := by dsimp only [σ₀]; linarith
    have hpos := Stage3ZeroFreeRegion.two_char_negLogDeriv_re_nonneg χ hσ₀1
    have hZ0 : (Stage3ZeroFreeRegion.negLogDerivZeta (σ₀ : ℂ)).re ≤ 1 / (4 * η) + 1 := by
      have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ₀1
      have hsub : σ₀ - 1 = 4 * η := by dsimp only [σ₀, δ]; ring
      rwa [hsub] at h
    obtain ⟨hM1, han, hnz, hbd, hzeros⟩ := hlandau_setup δ 0 hδ0 hδ4 (by norm_num)
    have hs₀_eq : ((1 + δ : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ) = (σ₀ : ℂ) := by simp [σ₀]
    rw [hs₀_eq] at han hnz hbd hzeros
    set M : ℝ := 16 * (q : ℝ) / δ
    have hconj_zero : DirichletCharacter.LFunction χ (starRingEnd ℂ s) = 0 := by
      rw [LFunction_conj_of_real hχ hreal (by linarith : 0 < s.re), hzero, map_zero]
    have hs_ne_conj : s ≠ starRingEnd ℂ s := by
      intro heq
      have := congrArg Complex.im heq
      simp only [Complex.conj_im] at this
      exact htim (by linarith)
    have hs_mem : s ∈ Metric.closedBall (σ₀ : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖s - (σ₀ : ℂ)‖ ≤ |(s - (σ₀ : ℂ)).re| + |(s - (σ₀ : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have hre : (s - (σ₀ : ℂ)).re = β - (1 + 4 * η) := by simp [σ₀, δ, β]
      have him : (s - (σ₀ : ℂ)).im = t := by simp [t]
      rw [hre, him, abs_of_neg (by linarith)] at h1
      linarith
    have hconj_mem : starRingEnd ℂ s ∈ Metric.closedBall (σ₀ : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : starRingEnd ℂ s - (σ₀ : ℂ) = starRingEnd ℂ (s - (σ₀ : ℂ)) := by simp
      rw [h1, Complex.norm_conj]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs_mem
    set S : Finset ℂ := {s, starRingEnd ℂ s}
    have hS : ∀ ρ ∈ S, ρ ∈ Metric.closedBall (σ₀ : ℂ) (1 / 4) ∧ DirichletCharacter.LFunction χ ρ = 0 := by
      intro ρ hρ
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hρ
      rcases hρ with rfl | rfl
      · exact ⟨hs_mem, hzero⟩
      · exact ⟨hconj_mem, hconj_zero⟩
    have hhalf : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
    have hlandau := Stage5ZetaZeroFree.landau_negLogDeriv_le_finset_zeros (R := 1 / 2) (M := M)
      (by norm_num) hM1 han hnz hbd (by rw [hhalf]; exact hzeros) S (by rw [hhalf]; exact hS)
    have hsum_S : ∑ ρ ∈ S, (1 / ((σ₀ : ℂ) - ρ)).re = 2 * (σ₀ - β) / ((σ₀ - β) ^ 2 + t ^ 2) := by
      dsimp only [S]
      rw [Finset.sum_pair hs_ne_conj]
      have h1 : (1 / ((σ₀ : ℂ) - s)).re = (σ₀ - β) / ((σ₀ - β) ^ 2 + t ^ 2) := by
        have hd : (σ₀ : ℂ) - s = ((σ₀ - β : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I :=
          Complex.ext (by simp [β]) (by simp [t])
        rw [hd, one_div, Complex.inv_re, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, zero_add,
          Complex.mul_im]
        ring
      have h2 : (1 / ((σ₀ : ℂ) - starRingEnd ℂ s)).re = (σ₀ - β) / ((σ₀ - β) ^ 2 + t ^ 2) := by
        have hd : (σ₀ : ℂ) - starRingEnd ℂ s = ((σ₀ - β : ℝ) : ℂ) + (t : ℂ) * I :=
          Complex.ext (by simp [β]) (by simp [t])
        rw [hd, one_div, Complex.inv_re, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, zero_add,
          Complex.mul_im]
        ring
      rw [h1, h2]; ring
    rw [hsum_S] at hlandau
    have h34_ge : (96 / 353 : ℝ) / η ≤ (3 / 4) * (2 * (σ₀ - β) / ((σ₀ - β) ^ 2 + t ^ 2)) := by
      have ha_lo : 4 * η ≤ σ₀ - β := by dsimp only [σ₀, δ]; linarith
      have ha_pos : 0 < σ₀ - β := by linarith
      have ha_hi : σ₀ - β ≤ (17 / 4) * η := by dsimp only [σ₀, δ]; linarith
      have ht2 : t ^ 2 ≤ 4 * η ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg t) hhigh.le 2
        rw [sq_abs] at this; linarith
      have hden_le : (σ₀ - β) ^ 2 + t ^ 2 ≤ (353 / 16 : ℝ) * η ^ 2 := by nlinarith
      have hnum_ge : 6 * η ≤ (3 / 4) * (2 * (σ₀ - β)) := by linarith
      have h1 : (96 / 353 : ℝ) / η = (6 * η) / ((353 / 16 : ℝ) * η ^ 2) := by
        field_simp [hη_pos.ne']; ring
      rw [h1, show (3 / 4 : ℝ) * (2 * (σ₀ - β) / ((σ₀ - β) ^ 2 + t ^ 2)) =
        ((3 / 4) * (2 * (σ₀ - β))) / ((σ₀ - β) ^ 2 + t ^ 2) by ring]
      exact div_le_div₀ (by positivity) hnum_ge (by positivity) hden_le
    have hlogM : Real.log M ≤ 4 * K₀ / 10000 + 10 + 2 * L := by
      have hMeq : M = (4 * K₀ / 10000) * 10000 * ((q : ℝ) * L) := by
        dsimp only [M, δ, η]; field_simp [hK₀_pos.ne', hL_pos.ne']; ring
      have hqL : (q : ℝ) * L ≤ (2 * (q : ℝ)) ^ 2 := by nlinarith
      have hMle : M ≤ (4 * K₀ / 10000) * 10000 * (2 * (q : ℝ)) ^ 2 := by rw [hMeq]; gcongr
      calc Real.log M ≤ Real.log ((4 * K₀ / 10000) * 10000 * (2 * (q : ℝ)) ^ 2) :=
            Real.log_le_log (by positivity) hMle
        _ = Real.log (4 * K₀ / 10000) + Real.log 10000 + Real.log ((2 * (q : ℝ)) ^ 2) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num)]
        _ = Real.log (4 * K₀ / 10000) + Real.log 10000 + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ 4 * K₀ / 10000 + 10 + 2 * L := by
            have := (Real.log_le_sub_one_of_pos (show 0 < 4 * K₀ / 10000 by positivity))
            linarith
    have hLχ : (Stage3ZeroFreeRegion.negLogDerivL χ (σ₀ : ℂ)).re ≤
        8 * Real.log M - (96 / 353 : ℝ) / η := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      have h8 : (4 : ℝ) / (1 / 2) = 8 := by norm_num
      rw [h8] at hlandau
      linarith
    have hinvη : 1 / η = K₀ * L := by dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
    have h14 : 1 / (4 * η) = (1 / 4) * (K₀ * L) := by dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
    have h96 : (96 / 353 : ℝ) / η = (96 / 353 : ℝ) * (K₀ * L) := by
      dsimp only [η]; field_simp [hK₀_pos.ne', hL_pos.ne']
    have hcomb : (31 / 1412 : ℝ) * (K₀ * L) ≤ 1 + 8 * (4 * K₀ / 10000 + 10 + 2 * L) := by linarith
    have hK₀L_ge : K₀ ≤ K₀ * L := by nlinarith
    nlinarith

/-! ### Section 2B: Estermann's Power-Series Proof of Siegel's Theorem (`0` Assumptions!) -/

/-- Real-valued `ArithmeticFunction` associated to a Dirichlet character `χ`. -/
private def charArithReal {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else (χ (n : ZMod q)).re
  map_zero' := by simp

private lemma charArithReal_isMultiplicative {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (charArithReal χ).IsMultiplicative := by
  refine ⟨by simp [charArithReal], fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [charArithReal]
  · by_cases hn : n = 0
    · subst hn; simp [charArithReal]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      simp only [charArithReal, ArithmeticFunction.coe_mk, if_neg hmn, if_neg hm, if_neg hn,
        Nat.cast_mul, map_mul, Complex.mul_re, hreal, mul_zero, sub_zero]

private lemma charArithReal_pow {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    charArithReal χ (p ^ k) = ((χ (p : ZMod q)).re) ^ k := by
  induction k with
  | zero => simp [charArithReal]
  | succ k ih =>
    have hpk : p ^ k ≠ 0 := pow_ne_zero k hp
    have hpks : p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hp
    simp only [charArithReal, ArithmeticFunction.coe_mk, if_neg hpks, if_neg hpk] at ih ⊢
    rw [pow_succ, Nat.cast_mul, map_mul, Complex.mul_re, hreal, hreal, mul_zero, sub_zero, ih]
    ring

/-- Elementary alternating sum identity:
`∑ j ∈ Finset.range (2 * m + 1), ((j + 1 : ℝ) * (2 * m - j + 1 : ℝ) * (-1 : ℝ) ^ (2 * m - j)) = m + 1`. -/
private lemma sum_alternating_linear_even (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 1),
        ((j : ℝ) + 1) * ((2 * (m : ℝ) - (j : ℝ)) + 1) * (-1 : ℝ) ^ (2 * m - j) =
      (m : ℝ) + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by omega
    rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
    have htail :
        (((2 * m + 1 : ℕ) : ℝ) + 1) * ((2 * ((m + 1 : ℕ) : ℝ) - ((2 * m + 1 : ℕ) : ℝ)) + 1) *
            (-1 : ℝ) ^ (2 * (m + 1) - (2 * m + 1)) +
          (((2 * m + 1 + 1 : ℕ) : ℝ) + 1) * ((2 * ((m + 1 : ℕ) : ℝ) - ((2 * m + 1 + 1 : ℕ) : ℝ)) + 1) *
            (-1 : ℝ) ^ (2 * (m + 1) - (2 * m + 1 + 1)) =
        -(2 * (m : ℝ) + 1) := by
      have h1 : 2 * (m + 1) - (2 * m + 1) = 1 := by omega
      have h2 : 2 * (m + 1) - (2 * m + 1 + 1) = 0 := by omega
      rw [h1, h2]; push_cast; ring
    have hfront :
        ∑ j ∈ Finset.range (2 * m + 1),
            ((j : ℝ) + 1) * ((2 * ((m + 1 : ℕ) : ℝ) - (j : ℝ)) + 1) * (-1 : ℝ) ^ (2 * (m + 1) - j) =
          (∑ j ∈ Finset.range (2 * m + 1),
            ((j : ℝ) + 1) * ((2 * (m : ℝ) - (j : ℝ)) + 1) * (-1 : ℝ) ^ (2 * m - j)) +
          2 * ∑ j ∈ Finset.range (2 * m + 1), ((j : ℝ) + 1) * (-1 : ℝ) ^ (2 * m - j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hexp : 2 * (m + 1) - j = (2 * m - j) + 2 := by omega
      rw [hexp, pow_add]
      push_cast; ring
    have hlin : ∀ n : ℕ, ∑ j ∈ Finset.range (2 * n + 1), ((j : ℝ) + 1) * (-1 : ℝ) ^ (2 * n - j) = (n : ℝ) + 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        have hs : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by omega
        rw [hs, Finset.sum_range_succ, Finset.sum_range_succ]
        have h1 : 2 * (n + 1) - (2 * n + 1) = 1 := by omega
        have h2 : 2 * (n + 1) - (2 * n + 1 + 1) = 0 := by omega
        have hcongr : ∑ j ∈ Finset.range (2 * n + 1), ((j : ℝ) + 1) * (-1 : ℝ) ^ (2 * (n + 1) - j) =
            ∑ j ∈ Finset.range (2 * n + 1), ((j : ℝ) + 1) * (-1 : ℝ) ^ (2 * n - j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjle : j ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hexp : 2 * (n + 1) - j = (2 * n - j) + 2 := by omega
          rw [hexp, pow_add]; norm_num
        rw [hcongr, ihn, h1, h2]; push_cast; ring
    rw [add_assoc, htail, hfront, ih, hlin m]
    push_cast; ring

/-- Non-negativity of the prime-power coefficient `∑_{j=0}^k c_j c_{k-j} v^{k-j}` for all
`u, v ∈ {0, 1, -1}` where `c_j = ∑_{i=0}^j u^i`. -/
private lemma four_char_primePow_coeff_nonneg {u v : ℝ}
    (hu : u = 0 ∨ u = 1 ∨ u = -1) (hv : v = 0 ∨ v = 1 ∨ v = -1) (k : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (k + 1),
      (∑ i ∈ Finset.range (j + 1), u ^ i) *
      (∑ r ∈ Finset.range (k - j + 1), u ^ r) * v ^ (k - j) := by
  have hc_nn : ∀ n : ℕ, 0 ≤ ∑ i ∈ Finset.range (n + 1), u ^ i := by
    intro n
    rcases hu with rfl | rfl | rfl
    · rw [Finset.sum_range_succ']
      simp
    · simp; positivity
    · induction n with
      | zero => simp
      | succ n ih =>
        rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
        · have h1 : (-1 : ℝ) ^ (n + 1) = 1 := by rw [hm, ← two_mul, pow_mul]; norm_num
          rw [Finset.sum_range_succ, h1]; linarith
        · have hsum0 : ∑ i ∈ Finset.range (2 * m + 1 + 1), (-1 : ℝ) ^ i = 0 := by
            clear ih hm
            induction m with
            | zero => simp
            | succ m ihm =>
              rw [show 2 * (m + 1) + 1 + 1 = 2 * m + 1 + 1 + 1 + 1 by omega,
                Finset.sum_range_succ, Finset.sum_range_succ, ihm]
              have h1 : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
                rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]; norm_num
              have h2 : (-1 : ℝ) ^ (2 * m + 1 + 1 + 1) = -1 := by
                rw [pow_succ, h1]; norm_num
              linarith
          rw [hm, hsum0]
  rcases hv with rfl | rfl | rfl
  · refine Finset.sum_nonneg fun j _ => ?_
    by_cases hkj : k - j = 0
    · rw [hkj, pow_zero, mul_one]; exact mul_nonneg (hc_nn j) (hc_nn 0)
    · rw [zero_pow hkj, mul_zero]
  · refine Finset.sum_nonneg fun j _ => ?_
    rw [one_pow, mul_one]; exact mul_nonneg (hc_nn j) (hc_nn (k - j))
  · rcases hu with rfl | rfl | rfl
    · have h0 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (0 : ℝ) ^ i = 1 := fun n => by
        rw [Finset.sum_range_succ']; simp
      simp_rw [h0, mul_one, one_mul]
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · have heq : ∑ j ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ (2 * m - j) = 1 := by
          clear hm
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ]
            have hcongr : ∑ j ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ (2 * (m + 1) - j) =
                ∑ j ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ (2 * m - j) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rw [show 2 * (m + 1) - j = (2 * m - j) + 2 by omega, pow_add]; norm_num
            have h1 : 2 * (m + 1) - (2 * m + 1) = 1 := by omega
            have h2 : 2 * (m + 1) - (2 * m + 1 + 1) = 0 := by omega
            rw [hcongr, ihm, h1, h2]; norm_num
        rw [show k = 2 * m by omega, heq]; norm_num
      · have heq : ∑ j ∈ Finset.range (2 * m + 1 + 1), (-1 : ℝ) ^ (2 * m + 1 - j) = 0 := by
          clear hm
          induction m with
          | zero => simp [Finset.sum_range_succ]
          | succ m ihm =>
            rw [show 2 * (m + 1) + 1 + 1 = 2 * m + 1 + 1 + 1 + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ]
            have hcongr : ∑ j ∈ Finset.range (2 * m + 1 + 1), (-1 : ℝ) ^ (2 * (m + 1) + 1 - j) =
                ∑ j ∈ Finset.range (2 * m + 1 + 1), (-1 : ℝ) ^ (2 * m + 1 - j) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjle : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rw [show 2 * (m + 1) + 1 - j = (2 * m + 1 - j) + 2 by omega, pow_add]; norm_num
            have h1 : 2 * (m + 1) + 1 - (2 * m + 1 + 1) = 1 := by omega
            have h2 : 2 * (m + 1) + 1 - (2 * m + 1 + 1 + 1) = 0 := by omega
            rw [hcongr, ihm, h1, h2]; norm_num
        rw [hm, heq]
    · have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (1 : ℝ) ^ i = (n : ℝ) + 1 := fun n => by
        simp [Finset.sum_const, nsmul_eq_mul]
      simp_rw [h1]
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hk2m : k = 2 * m := by omega
        subst hk2m
        have hcast :
            ∑ j ∈ Finset.range (2 * m + 1),
                ((j : ℝ) + 1) * (((2 * m - j : ℕ) : ℝ) + 1) * (-1 : ℝ) ^ (2 * m - j) =
              ∑ j ∈ Finset.range (2 * m + 1),
                ((j : ℝ) + 1) * ((2 * (m : ℝ) - (j : ℝ)) + 1) * (-1 : ℝ) ^ (2 * m - j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [Nat.cast_sub hjle]; push_cast; ring
        rw [hcast, sum_alternating_linear_even m]
        positivity
      · -- For odd `k`, reindexing `j ↦ k - j` negates the sum, so it equals `0`!
        have hneg :
            ∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) * (((k - j : ℕ) : ℝ) + 1) * (-1 : ℝ) ^ (k - j) =
              -(∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) * (((k - j : ℕ) : ℝ) + 1) * (-1 : ℝ) ^ (k - j)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
          · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_range] at hj₁ hj₂; omega
          · intro j hj; simp only [Finset.mem_range] at hj
            exact ⟨k - j, Finset.mem_range.mpr (by omega), by omega⟩
          · intro j hj
            simp only [Finset.mem_range] at hj
            have hsub : k - (k - j) = j := by omega
            rw [hsub]
            have hsign : (-1 : ℝ) ^ (k - j) = -((-1 : ℝ) ^ j) := by
              have hprod : (-1 : ℝ) ^ (k - j) * (-1 : ℝ) ^ j = -1 := by
                rw [← pow_add, show k - j + j = k by omega, hm, pow_succ, pow_mul]; norm_num
              have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
                rw [← mul_pow]; norm_num
              linear_combination ((-1 : ℝ) ^ j) * hprod - ((-1 : ℝ) ^ (k - j)) * hsq
            rw [hsign]; ring
        linarith
    · -- `u = -1, v = -1`: `c_n = 1` iff `Even n` and `0` iff `Odd n`, so every surviving term has `Even (k - j)` ⇒ `(-1)^(k-j) = 1`!
      refine Finset.sum_nonneg fun j _ => ?_
      have hc_alt : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i = if _root_.Even n then 1 else 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [Finset.sum_range_succ, ihn]
          rcases Nat.even_or_odd n with he | ho
          · have hodd : ¬ _root_.Even (n + 1) := by obtain ⟨r, hr⟩ := he; rintro ⟨s, hs⟩; omega
            have hp : (-1 : ℝ) ^ (n + 1) = -1 := by
              obtain ⟨r, hr⟩ := he; rw [hr, ← two_mul, pow_succ, pow_mul]; norm_num
            rw [if_pos he, if_neg hodd, hp]; ring
          · have hev : _root_.Even (n + 1) := by obtain ⟨r, hr⟩ := ho; exact ⟨r + 1, by omega⟩
            have hne : ¬ _root_.Even n := by obtain ⟨r, hr⟩ := ho; rintro ⟨s, hs⟩; omega
            have hp : (-1 : ℝ) ^ (n + 1) = 1 := by
              obtain ⟨r, hr⟩ := ho; rw [hr, show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
            rw [if_neg hne, if_pos hev, hp]; ring
      rw [hc_alt j, hc_alt (k - j)]
      by_cases h1 : _root_.Even j
      · by_cases h2 : _root_.Even (k - j)
        · rw [if_pos h1, if_pos h2, mul_one, one_mul]
          obtain ⟨r, hr⟩ := h2
          rw [hr, ← two_mul, pow_mul]; norm_num
        · rw [if_pos h1, if_neg h2, mul_zero, zero_mul]
      · rw [if_neg h1, zero_mul, zero_mul]

/-- The 4-character Dirichlet convolution `A = (ζ * χ₁) * (χ₂ * χ₁₂)` has non-negative coefficients
`0 ≤ A n` for all `n : ℕ` and `A 1 = 1` whenever `χ₁, χ₂` are real Dirichlet characters. -/
private lemma four_char_conv_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hreal1 : ∀ a : ZMod q₁, (χ₁ a).im = 0) (hreal2 : ∀ a : ZMod q₂, (χ₂ a).im = 0) :
    let A : ArithmeticFunction ℝ :=
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) *
      (charArithReal χ₂ * charArithReal (Stage3ZeroFreeRegion.prodChar χ₁ χ₂))
    A 1 = 1 ∧ ∀ n : ℕ, 0 ≤ A n := by
  intro A
  have hreal12 : ∀ a : ZMod (q₁ * q₂), (Stage3ZeroFreeRegion.prodChar χ₁ χ₂ a).im = 0 := by
    intro a
    rw [← ZMod.natCast_zmod_val a, Stage3ZeroFreeRegion.prodChar_apply_nat]
    simp [Complex.mul_im, hreal1, hreal2]
  have hzeta_mult : (ArithmeticFunction.zeta : ArithmeticFunction ℝ).IsMultiplicative := by
    refine ⟨by simp, fun {m n} _ => ?_⟩
    by_cases hm : m = 0
    · subst hm; simp
    · by_cases hn : n = 0
      · subst hn; simp
      · simp [ArithmeticFunction.zeta_apply_ne (mul_ne_zero hm hn),
          ArithmeticFunction.zeta_apply_ne hm, ArithmeticFunction.zeta_apply_ne hn]
  have hmult : A.IsMultiplicative :=
    (hzeta_mult.mul (charArithReal_isMultiplicative hreal1)).mul
      ((charArithReal_isMultiplicative hreal2).mul (charArithReal_isMultiplicative hreal12))
  refine ⟨hmult.1, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · clear hn
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp _ =>
      -- Evaluate `A (p ^ k)` explicitly via `Nat.divisorsAntidiagonal (p ^ k)`
      set u : ℝ := (χ₁ (p : ZMod q₁)).re
      set v : ℝ := (χ₂ (p : ZMod q₂)).re
      have hu : u = 0 ∨ u = 1 ∨ u = -1 := by
        rcases Stage7SiegelWalfisz.real_char_apply_trichotomy hreal1 (p : ZMod q₁) with h | h | h
        · left; simp [u, h]
        · right; left; simp [u, h]
        · right; right; simp [u, h]
      have hv : v = 0 ∨ v = 1 ∨ v = -1 := by
        rcases Stage7SiegelWalfisz.real_char_apply_trichotomy hreal2 (p : ZMod q₂) with h | h | h
        · left; simp [v, h]
        · right; left; simp [v, h]
        · right; right; simp [v, h]
      have hconv_pp : ∀ (f g : ArithmeticFunction ℝ) (m : ℕ),
          (f * g) (p ^ m) = ∑ i ∈ Finset.range (m + 1), f (p ^ i) * g (p ^ (m - i)) := by
        intro f g m
        rw [ArithmeticFunction.mul_apply]
        symm
        refine Finset.sum_bij (fun i _ => (p ^ i, p ^ (m - i))) ?_ ?_ ?_ ?_
        · intro i hi
          have hile : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨by rw [← pow_add, show i + (m - i) = m by omega], pow_ne_zero m hp.ne_zero⟩
        · intro i₁ _ i₂ _ h
          have h1 : p ^ i₁ = p ^ i₂ := congrArg Prod.fst h
          exact Nat.pow_right_injective hp.two_le h1
        · intro x hx
          rw [Nat.mem_divisorsAntidiagonal] at hx
          have hxdvd : x.1 ∣ p ^ m := ⟨x.2, hx.1.symm⟩
          obtain ⟨i, hile, hx1⟩ := (Nat.dvd_prime_pow hp).mp hxdvd
          refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
          refine Prod.ext hx1.symm ?_
          have hmul : p ^ i * x.2 = p ^ i * p ^ (m - i) := by
            calc p ^ i * x.2 = x.1 * x.2 := by rw [hx1]
              _ = p ^ m := hx.1
              _ = p ^ (i + (m - i)) := by rw [show i + (m - i) = m by omega]
              _ = p ^ i * p ^ (m - i) := pow_add p i (m - i)
          exact (Nat.mul_left_cancel (pow_pos hp.pos i) hmul).symm
        · intro _ _; rfl
      have hf1' : ∀ j : ℕ, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) (p ^ j) =
          ∑ i ∈ Finset.range (j + 1), u ^ i := by
        intro j
        rw [hconv_pp]
        refine Finset.sum_bij (fun i _ => j - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i₁ hi₁ i₂ hi₂ h; simp only [Finset.mem_range] at hi₁ hi₂; omega
        · intro i hi; simp only [Finset.mem_range] at hi
          exact ⟨j - i, Finset.mem_range.mpr (by omega), by omega⟩
        · intro i hi
          have hpi : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
          rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hpi,
            Nat.cast_one, one_mul, charArithReal_pow hreal1 hp.ne_zero (j - i)]
      have hf2' : ∀ m : ℕ,
          (charArithReal χ₂ * charArithReal (Stage3ZeroFreeRegion.prodChar χ₁ χ₂)) (p ^ m) =
            (∑ r ∈ Finset.range (m + 1), u ^ r) * v ^ m := by
        intro m
        rw [hconv_pp, Finset.sum_mul]
        refine Finset.sum_bij (fun i _ => m - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i₁ hi₁ i₂ hi₂ h; simp only [Finset.mem_range] at hi₁ hi₂; omega
        · intro r hr; simp only [Finset.mem_range] at hr
          exact ⟨m - r, Finset.mem_range.mpr (by omega), by omega⟩
        · intro i hi
          have hile : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [charArithReal_pow hreal2 hp.ne_zero i,
            charArithReal_pow hreal12 hp.ne_zero (m - i)]
          have hprod_re : (Stage3ZeroFreeRegion.prodChar χ₁ χ₂ (p : ZMod (q₁ * q₂))).re = u * v := by
            rw [Stage3ZeroFreeRegion.prodChar_apply_nat, Complex.mul_re, hreal1, hreal2]
            simp [u, v]
          rw [hprod_re, mul_pow]
          have hvp : v ^ i * v ^ (m - i) = v ^ m := by rw [← pow_add, show i + (m - i) = m by omega]
          calc v ^ i * (u ^ (m - i) * v ^ (m - i)) = u ^ (m - i) * (v ^ i * v ^ (m - i)) := by ring
            _ = u ^ (m - i) * v ^ m := by rw [hvp]
      dsimp only [A]
      rw [hconv_pp]
      have hrewrite :
          ∑ j ∈ Finset.range (k + 1),
              ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) (p ^ j) *
                (charArithReal χ₂ * charArithReal (Stage3ZeroFreeRegion.prodChar χ₁ χ₂)) (p ^ (k - j)) =
            ∑ j ∈ Finset.range (k + 1),
              (∑ i ∈ Finset.range (j + 1), u ^ i) *
              (∑ r ∈ Finset.range (k - j + 1), u ^ r) * v ^ (k - j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hf1' j, hf2' (k - j)]; ring
      rw [hrewrite]
      exact four_char_primePow_coeff_nonneg hu hv k
    | zero => simp
    | one => rw [hmult.1]; norm_num
    | coprime a b _ _ hcop hAa hAb =>
      rw [hmult.2 hcop]
      exact mul_nonneg hAa hAb

/-- Elementary Cauchy estimate for power-series coefficients from a sphere bound `‖H z‖ ≤ M`
on `Metric.sphere z₀ R`. -/
private lemma cauchy_powerSeries_coeff_norm_le {H : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (_hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ H (Metric.closedBall z₀ R))
    (hsphere : ∀ z ∈ Metric.sphere z₀ R, ‖H z‖ ≤ M) (k : ℕ) :
    ‖iteratedDeriv k H z₀ / (k.factorial : ℂ)‖ ≤ M / R ^ k := by
  set Rnn : NNReal := ⟨R, hR.le⟩
  have hp := hdiff.hasFPowerSeriesOnBall (show (0 : NNReal) < Rnn from hR)
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k H z₀ / (k.factorial : ℂ) = cauchyPowerSeries H z₀ R k (fun _ => 1) := by
    rw [show (Rnn : ℝ) = R from rfl] at key
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  have hint_le : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖H (circleMap z₀ R θ)‖ ≤ M := by
    have hcont : ContinuousOn (fun θ : ℝ => ‖H (circleMap z₀ R θ)‖) (Set.uIcc 0 (2 * Real.pi)) := by
      refine (hdiff.continuousOn.comp (continuous_circleMap z₀ R).continuousOn fun θ _ => ?_).norm
      exact Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ)
    have h1 : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖H (circleMap z₀ R θ)‖ ≤
        ∫ _θ in (0 : ℝ)..2 * Real.pi, M := by
      refine intervalIntegral.integral_mono_on (by positivity) hcont.intervalIntegrable
        intervalIntegrable_const fun θ _ => hsphere _ (circleMap_mem_sphere z₀ hR.le θ)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖H (circleMap z₀ R θ)‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M := by field_simp [Real.pi_ne_zero]
  calc ‖cauchyPowerSeries H z₀ R k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries H z₀ R k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries H z₀ R k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖H (circleMap z₀ R θ)‖) * |R|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le H z₀ R k
    _ ≤ M * |R|⁻¹ ^ k := mul_le_mul_of_nonneg_right hint_le (by positivity)
    _ = M / R ^ k := by rw [abs_of_pos hR, inv_pow, div_eq_mul_inv]

/-- **Core Estermann Inequality for Two Distinct Real Primitive Characters**:
if `χ₁ mod q₁` and `χ₂ mod q₂` are distinct real non-principal primitive characters and
`LFunction χ₁ β₁ = 0` with `1 - 1/16 < β₁ < 1`, then for `M_H = 15000 * q₁² * q₂²` and every `N : ℕ`:
`((LFunction χ₁ 1).re * (LFunction χ₂ 1).re * (LFunction (prodChar χ₁ χ₂) 1).re) * (2 - β₁) ^ N / (1 - β₁) ≥ 1 - 6 * M_H * (5 / 6) ^ N`. -/
private theorem estermann_key_inequality {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (h1_ne : χ₁ ≠ 1) (h2_ne : χ₂ ≠ 1)
    (hreal1 : ∀ a : ZMod q₁, (χ₁ a).im = 0) (hreal2 : ∀ a : ZMod q₂, (χ₂ a).im = 0)
    (hne : PChar.of χ₁ ≠ PChar.of χ₂)
    {β₁ : ℝ} (hβ_lo : 1 - 1 / 16 < β₁) (hβ_hi : β₁ < 1)
    (hz1 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0) (N : ℕ) :
    let χ₁₂ := Stage3ZeroFreeRegion.prodChar χ₁ χ₂
    let lam : ℝ := (DirichletCharacter.LFunction χ₁ 1).re *
      (DirichletCharacter.LFunction χ₂ 1).re * (DirichletCharacter.LFunction χ₁₂ 1).re
    let M_H : ℝ := 15000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2
    1 - 6 * M_H * (5 / 6 : ℝ) ^ N ≤ lam * (2 - β₁) ^ N / (1 - β₁) := by
  intro χ₁₂ lam M_H
  have hreal12 : ∀ a : ZMod (q₁ * q₂), (χ₁₂ a).im = 0 := by
    intro a
    rw [← ZMod.natCast_zmod_val a, Stage3ZeroFreeRegion.prodChar_apply_nat]
    simp [Complex.mul_im, hreal1, hreal2]
  set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
  set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
  have hψ_ne : ψ₁ ≠ ψ₂ := fun h => hne (by rw [show PChar.of χ₁ = ψ₁ from PChar.of_self ψ₁,
    show PChar.of χ₂ = ψ₂ from PChar.of_self ψ₂, h])
  have h12_ne : χ₁₂ ≠ 1 :=
    Stage3ZeroFreeRegion.prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
  have hL1_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₁ h1_ne hreal1
  have hL2_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₂ h2_ne hreal2
  have hL12_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₁₂ h12_ne hreal12
  have hlam_pos : 0 < lam := mul_pos (mul_pos hL1_pos.1 hL2_pos.1) hL12_pos.1
  have hlamC : (lam : ℂ) = DirichletCharacter.LFunction χ₁ 1 *
      DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction χ₁₂ 1 := by
    apply Complex.ext
    · simp [lam, Complex.mul_re, hL1_pos.2, hL2_pos.2, hL12_pos.2]
    · simp [lam, Complex.mul_im, hL1_pos.2, hL2_pos.2, hL12_pos.2]
  set F : ℂ → ℂ := fun s =>
    riemannZeta s * DirichletCharacter.LFunction χ₁ s *
    DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction χ₁₂ s
  set G : ℂ → ℂ := fun s =>
    Stage6EffectivePNT.zetaReg s * DirichletCharacter.LFunction χ₁ s *
    DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction χ₁₂ s
  set H : ℂ → ℂ := dslope G 1
  have hG_one : G 1 = (lam : ℂ) := by
    dsimp only [G]
    rw [Stage6EffectivePNT.zetaReg_one, one_mul, hlamC]
  have hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re} := by
    have hd1 : DifferentiableOn ℂ (DirichletCharacter.LFunction χ₁) {s : ℂ | 0 < s.re} :=
      (DirichletCharacter.differentiable_LFunction h1_ne).differentiableOn
    have hd2 : DifferentiableOn ℂ (DirichletCharacter.LFunction χ₂) {s : ℂ | 0 < s.re} :=
      (DirichletCharacter.differentiable_LFunction h2_ne).differentiableOn
    have hd12 : DifferentiableOn ℂ (DirichletCharacter.LFunction χ₁₂) {s : ℂ | 0 < s.re} :=
      (DirichletCharacter.differentiable_LFunction h12_ne).differentiableOn
    exact ((Stage6EffectivePNT.differentiableOn_zetaReg.mul hd1).mul hd2).mul hd12
  have hH_diff : DifferentiableOn ℂ H {s : ℂ | 0 < s.re} :=
    (Complex.differentiableOn_dslope
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))).mpr hG_diff
  have hH_eq : ∀ s : ℂ, 0 < s.re → s ≠ 1 → H s = F s - (lam : ℂ) / (s - 1) := by
    intro s hs hs1
    dsimp only [H]
    rw [dslope_of_ne G hs1, slope_def_field, hG_one]
    dsimp only [G, F]
    rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hs hs1]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [hsub]
  -- Bound `‖H z‖ ≤ M_H` on `Metric.sphere (2 : ℂ) (3 / 2)`
  have hcb_sub : Metric.closedBall (2 : ℂ) (3 / 2) ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - 2)).trans hz)
    simp only [Complex.sub_re, Complex.re_ofNat] at hre
    change 0 < z.re; linarith
  have hsphere_bd : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖H z‖ ≤ M_H := by
    intro z hz
    have hz_dist : ‖z - 2‖ = 3 / 2 := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - 2)).trans hz_dist.le)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - 2)).trans hz_dist.le)
    simp only [Complex.sub_re, Complex.re_ofNat, Complex.sub_im, Complex.im_ofNat, sub_zero] at hre_diff him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 7 / 2 := by linarith
    have hz_im : |z.im| ≤ 3 / 2 := abs_le.mpr him_diff
    have hz1_ge : 1 / 2 ≤ ‖z - 1‖ := by
      have htri : ‖z - 2‖ ≤ ‖z - 1‖ + ‖(-1 : ℂ)‖ := by
        simpa [show z - 1 + (-1 : ℂ) = z - 2 by ring] using norm_add_le (z - 1) (-1 : ℂ)
      rw [hz_dist, norm_neg, norm_one] at htri; linarith
    have hz_ne1 : z ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hz1_ge; linarith
    rw [hH_eq z (by linarith) hz_ne1]
    have hZ_bd : ‖riemannZeta z‖ ≤ 13 := by
      have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith : 0 < z.re) hz_ne1
      have hinv : 1 / ‖z - 1‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have hnormz : ‖z‖ ≤ 5 := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos (by linarith : 0 < z.re)] at this; linarith
      have hdivz : ‖z‖ / z.re ≤ 10 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hL_bd : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ‖DirichletCharacter.LFunction χ z‖ ≤ 10 * (q : ℝ) := by
      intro q _ χ hχ
      have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
        (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
        (by linarith : 0 < z.re)
      calc ‖DirichletCharacter.LFunction χ z‖
          ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
        _ ≤ (q : ℝ) * (7 / 2 + 3 / 2) / (1 / 2) :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q))
              (by norm_num) hz_re_lo
        _ = 10 * (q : ℝ) := by ring
    have hF_bd : ‖F z‖ ≤ 13000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by
      dsimp only [F]
      simp only [norm_mul]
      have h1 := hL_bd χ₁ h1_ne
      have h2 := hL_bd χ₂ h2_ne
      have h12 := hL_bd χ₁₂ h12_ne
      push_cast at h12
      calc ‖riemannZeta z‖ * ‖DirichletCharacter.LFunction χ₁ z‖ *
              ‖DirichletCharacter.LFunction χ₂ z‖ * ‖DirichletCharacter.LFunction χ₁₂ z‖
          ≤ 13 * (10 * (q₁ : ℝ)) * (10 * (q₂ : ℝ)) * (10 * ((q₁ : ℝ) * (q₂ : ℝ))) := by
            gcongr
        _ = 13000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by ring
    have hlam_bd : lam ≤ 1000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by
      have h1_le : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
          (DirichletCharacter.LFunction χ 1).re ≤ 10 * (q : ℝ) := by
        intro q _ χ hχ
        have h := Stage5DirichletLZeroFree.norm_LFunction_le_log_of_one_le_re hχ (s := 1) (by simp) (by simp)
        simp only [Complex.one_im, abs_zero, zero_add] at h
        have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
        have hlog : Real.log ((q : ℝ) * 2) ≤ 2 * (q : ℝ) :=
          (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        calc (DirichletCharacter.LFunction χ 1).re
            ≤ ‖DirichletCharacter.LFunction χ 1‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ 5 * Real.log ((q : ℝ) * 2) := h
          _ ≤ 10 * (q : ℝ) := by linarith
      have b1 := h1_le χ₁ h1_ne
      have b2 := h1_le χ₂ h2_ne
      have b12 := h1_le χ₁₂ h12_ne
      push_cast at b12
      dsimp only [lam]
      calc (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              (DirichletCharacter.LFunction χ₁₂ 1).re
          ≤ (10 * (q₁ : ℝ)) * (10 * (q₂ : ℝ)) * (10 * ((q₁ : ℝ) * (q₂ : ℝ))) := by
            refine mul_le_mul (mul_le_mul b1 b2 hL2_pos.1.le (by positivity)) b12 hL12_pos.1.le (by positivity)
        _ = 1000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by ring
    have hpole_bd : ‖(lam : ℂ) / (z - 1)‖ ≤ 2000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      calc lam / ‖z - 1‖ ≤ (1000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2) / (1 / 2) :=
            div_le_div₀ (by positivity) hlam_bd (by norm_num) hz1_ge
        _ = 2000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by ring
    calc ‖F z - (lam : ℂ) / (z - 1)‖
        ≤ ‖F z‖ + ‖(lam : ℂ) / (z - 1)‖ := norm_sub_le _ _
      _ ≤ 13000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 + 2000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2 := by linarith
      _ = M_H := by dsimp only [M_H]; ring
  -- Taylor series of `H` centered at `2` with radius `3 / 2`, evaluated at `β₁`
  have hH_cb : DifferentiableOn ℂ H (Metric.closedBall (2 : ℂ) (3 / 2)) := hH_diff.mono hcb_sub
  set Rnn : NNReal := ⟨3 / 2, by norm_num⟩
  have hRnn_pos : (0 : NNReal) < Rnn := by
    change (0 : ℝ) < (3 / 2 : ℝ); norm_num
  have hRnn_coe : (Rnn : ℝ) = 3 / 2 := rfl
  have hps := hH_cb.hasFPowerSeriesOnBall hRnn_pos
  have hβ_in_ball : ((β₁ : ℂ) - 2) ∈ Metric.eball (0 : ℂ) Rnn := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    have hnorm : ‖(β₁ : ℂ) - 2‖ = 2 - β₁ := by
      rw [show (β₁ : ℂ) - 2 = (((β₁ - 2 : ℝ) : ℂ)) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    exact_mod_cast (show ‖(β₁ : ℂ) - 2‖ < (3 / 2 : ℝ) by rw [hnorm]; linarith)
  have hhasSum := hps.hasSum hβ_in_ball
  rw [add_sub_cancel, hRnn_coe] at hhasSum
  -- Express each Taylor term via `iteratedDeriv k H 2 / k!`
  have hterm_eq : ∀ k : ℕ,
      cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2) =
        (iteratedDeriv k H 2 / (k.factorial : ℂ)) * ((β₁ : ℂ) - 2) ^ k := by
    intro k
    have h1 := (cauchyPowerSeries H 2 (3 / 2 : ℝ) k).map_smul_univ (fun _ => ((β₁ : ℂ) - 2)) (fun _ => (1 : ℂ))
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have key := hps.factorial_smul (1 : ℂ) k
    rw [hRnn_coe] at key
    have hderiv : iteratedDeriv k H 2 / (k.factorial : ℂ) = cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => 1) := by
      rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
      have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      field_simp
    rw [h1, ← hderiv]; ring
  -- Identify `F` with `LSeries A` on `Re(s) > 1` and get nonnegativity of `(-1)^k F^{(k)}(2)`!
  set A : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) *
    (charArithReal χ₂ * charArithReal χ₁₂)
  obtain ⟨hA1, hA_nn⟩ := four_char_conv_nonneg hreal1 hreal2
  have hF_eq_LSeries : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (fun n => (A n : ℂ)) s ∧ F s = LSeries (fun n => (A n : ℂ)) s := by
    intro s hs
    have hSZ : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℂ)) s := by
      have h := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
      refine h.congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp only [LSeries.term_of_ne_zero hn.ne', ArithmeticFunction.zeta_apply_ne hn.ne',
          ArithmeticFunction.natCoe_apply, Nat.cast_one, Complex.ofReal_one]
    have hS_char : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), (∀ a, (χ a).im = 0) →
        LSeriesSummable (fun n => (charArithReal χ n : ℂ)) s ∧
        DirichletCharacter.LFunction χ s = LSeries (fun n => (charArithReal χ n : ℂ)) s := by
      intro q _ χ hreal
      have hcongr : ∀ {n : ℕ}, n ≠ 0 → (charArithReal χ n : ℂ) = χ (n : ZMod q) := fun {n} hn => by
        simp only [charArithReal, ArithmeticFunction.coe_mk, if_neg hn]
        exact Complex.ext (by simp) (by simp [hreal])
      have hsum : LSeriesSummable (fun n => χ (n : ZMod q)) s :=
        DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
      refine ⟨?_, ?_⟩
      · exact (LSeriesSummable_congr s fun hn => (hcongr hn).symm).mp hsum
      · rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
        exact LSeries_congr (fun hn => (hcongr hn).symm) s
    obtain ⟨hS1, hL1⟩ := hS_char χ₁ hreal1
    obtain ⟨hS2, hL2⟩ := hS_char χ₂ hreal2
    obtain ⟨hS12, hL12⟩ := hS_char χ₁₂ hreal12
    have hconv_cast : ∀ (f g : ArithmeticFunction ℝ) (n : ℕ),
        ((f * g) n : ℂ) = LSeries.convolution (fun k => (f k : ℂ)) (fun k => (g k : ℂ)) n := by
      intro f g n
      rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, LSeries.convolution_def]
      refine Finset.sum_congr rfl fun p _ => by push_cast; rfl
    have hS01 : LSeriesSummable (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) n : ℂ)) s :=
      (LSeriesSummable_congr s fun {n} _ => (hconv_cast _ _ n).symm).mp (LSeriesSummable.convolution hSZ hS1)
    have hS212 : LSeriesSummable (fun n => ((charArithReal χ₂ * charArithReal χ₁₂) n : ℂ)) s :=
      (LSeriesSummable_congr s fun {n} _ => (hconv_cast _ _ n).symm).mp (LSeriesSummable.convolution hS2 hS12)
    have hSA : LSeriesSummable (fun n => (A n : ℂ)) s :=
      (LSeriesSummable_congr s fun {n} _ => (hconv_cast _ _ n).symm).mp (LSeriesSummable.convolution hS01 hS212)
    have hLZ : riemannZeta s = LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℂ)) s := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs]
      unfold LSeries
      refine tsum_congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow (fun h0 => by rw [h0, Complex.zero_re] at hs; linarith), div_zero]
      · simp only [LSeries.term_of_ne_zero hn.ne', ArithmeticFunction.natCoe_apply,
          ArithmeticFunction.zeta_apply_ne hn.ne', Nat.cast_one, Complex.ofReal_one]
    refine ⟨hSA, ?_⟩
    have hL01 : LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) n : ℂ)) s =
        riemannZeta s * DirichletCharacter.LFunction χ₁ s := by
      rw [hLZ, hL1, ← LSeries_convolution' hSZ hS1]
      exact LSeries_congr (fun {n} _ => hconv_cast _ _ n) s
    have hL212 : LSeries (fun n => ((charArithReal χ₂ * charArithReal χ₁₂) n : ℂ)) s =
        DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction χ₁₂ s := by
      rw [hL2, hL12, ← LSeries_convolution' hS2 hS12]
      exact LSeries_congr (fun {n} _ => hconv_cast _ _ n) s
    have hLA : LSeries (fun n => (A n : ℂ)) s =
        LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charArithReal χ₁) n : ℂ)) s *
        LSeries (fun n => ((charArithReal χ₂ * charArithReal χ₁₂) n : ℂ)) s := by
      rw [← LSeries_convolution' hS01 hS212]
      exact LSeries_congr (fun {n} _ => hconv_cast _ _ n) s
    dsimp only [F]
    rw [hLA, hL01, hL212]; ring
  have hF_deriv_nonneg : ∀ k : ℕ, 0 ≤ ((-1 : ℂ) ^ k * iteratedDeriv k F 2).re ∧
      (k = 0 → 1 ≤ (F 2).re) := by
    intro k
    have hconv : ∀ x : ℝ, (1 : ℝ) < x → LSeriesSummable (fun n => (A n : ℂ)) (x : ℂ) :=
      fun x hx => (hF_eq_LSeries (x : ℂ) (by simpa using hx)).1
    have hev : F =ᶠ[𝓝 (2 : ℂ)] Stage3RealAnalyticLandau.dirSeries (fun n => A n) := by
      have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
      rw [(hF_eq_LSeries s hs).2, Stage3RealAnalyticLandau.dirSeries_eq_LSeries]
    have hderiv_eq : iteratedDeriv k F 2 =
        iteratedDeriv k (Stage3RealAnalyticLandau.dirSeries (fun n => A n)) ((2 : ℝ) : ℂ) := by
      simpa using hev.iteratedDeriv_eq k
    have halt := Stage3RealAnalyticLandau.alternating_iteratedDeriv_dirSeries_real
      (a := fun n => A n) (by simp) hconv (by norm_num : (1 : ℝ) < 2) k
    have hsumm := Stage3RealAnalyticLandau.summable_log_pow_mul_rpow
      (a := fun n => A n) (by simp) hA_nn hconv (by norm_num : (1 : ℝ) < 2) k
    rw [hderiv_eq, halt, Complex.ofReal_re]
    refine ⟨tsum_nonneg fun n => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
        exact mul_nonneg (mul_nonneg (hA_nn n) (pow_nonneg (Real.log_nonneg hn1) k))
          (Real.rpow_nonneg (zero_le_one.trans hn1) (-2 : ℝ))
    · rintro rfl
      have hF2 : F 2 = ((∑' n : ℕ, A n * (Real.log (n : ℝ)) ^ 0 * (n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
        rw [← hderiv_eq, pow_zero, one_mul, iteratedDeriv_zero] at halt
        exact halt
      rw [hF2, Complex.ofReal_re]
      have hterm1 : (1 : ℝ) = A 1 * (Real.log ((1 : ℕ) : ℝ)) ^ 0 * ((1 : ℕ) : ℝ) ^ (-2 : ℝ) := by
        rw [hA1]; simp
      rw [hterm1]
      exact hsumm.le_tsum 1 fun n _ => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · exact mul_nonneg (mul_nonneg (hA_nn n) (by norm_num)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- Compute `(c_k * (β₁ - 2)^k).re` lower bound!
  have hterm_lower : ∀ k : ℕ,
      (if k = 0 then (1 : ℝ) else 0) - lam * (2 - β₁) ^ k ≤
        (cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2)).re := by
    intro k
    rw [hterm_eq k]
    have hopen : IsOpen ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    have hloc : H =ᶠ[𝓝 (2 : ℂ)] fun s => F s - (lam : ℂ) * (s - 1)⁻¹ := by
      filter_upwards [hopen.mem_nhds ⟨by norm_num, by norm_num⟩] with s hs
      rw [hH_eq s hs.1 hs.2, div_eq_mul_inv]
    have hFc : ContDiffAt ℂ k F 2 := by
      have hF_diff : DifferentiableOn ℂ F ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
        have hZ : DifferentiableOn ℂ riemannZeta ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) :=
          fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt
        exact ((hZ.mul
          (DirichletCharacter.differentiable_LFunction h1_ne).differentiableOn).mul
          (DirichletCharacter.differentiable_LFunction h2_ne).differentiableOn).mul
          (DirichletCharacter.differentiable_LFunction h12_ne).differentiableOn
      exact (hF_diff.contDiffOn hopen).contDiffAt (hopen.mem_nhds ⟨by norm_num, by norm_num⟩)
    have hPc : ContDiffAt ℂ k (fun s : ℂ => (lam : ℂ) * (s - 1)⁻¹) 2 :=
      contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
    have hPderiv : iteratedDeriv k (fun s : ℂ => (lam : ℂ) * (s - 1)⁻¹) 2 =
        (lam : ℂ) * ((-1 : ℂ) ^ k * (k.factorial : ℂ)) := by
      rw [iteratedDeriv_const_mul_field]; congr 1
      have hinv : ∀ m : ℕ, ∀ z : ℂ, z ≠ 0 →
          iteratedDeriv m (fun w : ℂ => w⁻¹) z = (-1 : ℂ) ^ m * (m.factorial : ℂ) * z ^ (-(m + 1 : ℤ)) := by
        intro m
        induction m with
        | zero => intro z _; simp
        | succ m ihm =>
          intro z hz
          rw [iteratedDeriv_succ]
          have hev_z : iteratedDeriv m (fun w : ℂ => w⁻¹) =ᶠ[𝓝 z]
              fun w => (-1 : ℂ) ^ m * (m.factorial : ℂ) * w ^ (-(m + 1 : ℤ)) := by
            filter_upwards [isOpen_ne.mem_nhds hz] with w hw
            exact ihm w hw
          rw [hev_z.deriv_eq]
          have hd : HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) * w ^ (-(m + 1 : ℤ)))
              ((-1 : ℂ) ^ m * (m.factorial : ℂ) * (((-(m + 1 : ℤ) : ℤ) : ℂ) * z ^ (-(m + 1 : ℤ) - 1))) z :=
            (hasDerivAt_zpow (-(m + 1 : ℤ)) z (Or.inl hz)).const_mul _
          rw [hd.deriv, pow_succ, Nat.factorial_succ]
          have hexp1 : (-(m + 1 : ℤ) - 1) = -((m : ℤ) + 1 + 1) := by omega
          have hexp2 : -(((m + 1 : ℕ) : ℤ) + 1) = -((m : ℤ) + 1 + 1) := by push_cast; omega
          rw [hexp1, hexp2]
          push_cast; ring
      have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) (1 : ℂ)) (2 : ℂ)
      rw [e, hinv k (2 - 1) (by norm_num)]
      norm_num
    rw [hloc.iteratedDeriv_eq k, iteratedDeriv_fun_sub hFc hPc, hPderiv]
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hβ_sub : ((β₁ : ℂ) - 2) ^ k = (-1 : ℂ) ^ k * (((2 - β₁) ^ k : ℝ) : ℂ) := by
      have : (β₁ : ℂ) - 2 = (-1 : ℂ) * ((2 - β₁ : ℝ) : ℂ) := by push_cast; ring
      rw [this, mul_pow, Complex.ofReal_pow]
    have halg :
        ((iteratedDeriv k F 2 - (lam : ℂ) * ((-1 : ℂ) ^ k * (k.factorial : ℂ))) / (k.factorial : ℂ)) *
            ((β₁ : ℂ) - 2) ^ k =
          ((((2 - β₁) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)) * ((-1 : ℂ) ^ k * iteratedDeriv k F 2) -
          (((lam * (2 - β₁) ^ k : ℝ) : ℂ)) := by
      rw [hβ_sub]
      have hsq1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
      push_cast
      field_simp [hfac]
      linear_combination (-(lam : ℂ) * (k.factorial : ℂ) * ((2 : ℂ) - (β₁ : ℂ)) ^ k) * hsq1
    rw [halg, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    have hF_nn := (hF_deriv_nonneg k).1
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
        iteratedDeriv_zero]
      linarith [(hF_deriv_nonneg 0).2 rfl]
    · simp only [if_neg hk0]
      have hcoeff_nn : 0 ≤ (2 - β₁) ^ k / (k.factorial : ℝ) := by
        have : 0 ≤ 2 - β₁ := by linarith
        positivity
      linarith [mul_nonneg hcoeff_nn hF_nn]
  -- Split the convergent Taylor series of `H β₁` at `N`!
  have hH_β₁ : (H (β₁ : ℂ)).re = lam / (1 - β₁) := by
    rw [hH_eq (β₁ : ℂ) (by simp; linarith) (fun h => hβ_hi.ne (by simpa using congrArg Complex.re h))]
    have hFβ : F (β₁ : ℂ) = 0 := by dsimp only [F]; rw [hz1, mul_zero, zero_mul, zero_mul]
    rw [hFβ, zero_sub, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.neg_re, Complex.ofReal_re]
    field_simp [(by linarith : 1 - β₁ ≠ 0), (by linarith : β₁ - 1 ≠ 0)]
    ring
  have hsum_re : HasSum (fun k : ℕ => (cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2)).re)
      (H (β₁ : ℂ)).re := Complex.reCLM.hasSum hhasSum
  have hsum_eq : lam / (1 - β₁) =
      (∑ k ∈ Finset.range N, (cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2)).re) +
      ∑' k : ℕ, (cauchyPowerSeries H 2 (3 / 2 : ℝ) (k + N) (fun _ => (β₁ : ℂ) - 2)).re := by
    rw [← hH_β₁, ← hsum_re.tsum_eq]
    exact (Summable.sum_add_tsum_nat_add N hsum_re.summable).symm
  -- Tail upper bound `≤ 6 * M_H * (5 / 6)^N`
  have htail_le :
      |∑' k : ℕ, (cauchyPowerSeries H 2 (3 / 2 : ℝ) (k + N) (fun _ => (β₁ : ℂ) - 2)).re| ≤
        6 * M_H * (5 / 6 : ℝ) ^ N := by
    have hM_nn : 0 ≤ M_H := by positivity
    have hnorm_term : ∀ m : ℕ,
        ‖(cauchyPowerSeries H 2 (3 / 2 : ℝ) m (fun _ => (β₁ : ℂ) - 2)).re‖ ≤
          M_H * (5 / 6 : ℝ) ^ m := by
      intro m
      rw [Real.norm_eq_abs, hterm_eq m]
      have h1 := cauchy_powerSeries_coeff_norm_le (R := 3 / 2) (M := M_H) (by norm_num) hM_nn hH_cb hsphere_bd m
      have h2 : ‖((β₁ : ℂ) - 2) ^ m‖ = (2 - β₁) ^ m := by
        rw [norm_pow, show (β₁ : ℂ) - 2 = (((β₁ - 2 : ℝ) : ℂ)) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        ring
      have hrat : (2 - β₁) / (3 / 2 : ℝ) ≤ 5 / 6 := by linarith
      calc |((iteratedDeriv m H 2 / (m.factorial : ℂ)) * ((β₁ : ℂ) - 2) ^ m).re|
          ≤ ‖(iteratedDeriv m H 2 / (m.factorial : ℂ)) * ((β₁ : ℂ) - 2) ^ m‖ := Complex.abs_re_le_norm _
        _ = ‖iteratedDeriv m H 2 / (m.factorial : ℂ)‖ * (2 - β₁) ^ m := by rw [norm_mul, h2]
        _ ≤ (M_H / (3 / 2 : ℝ) ^ m) * (2 - β₁) ^ m := mul_le_mul_of_nonneg_right h1 (pow_nonneg (by linarith) m)
        _ = M_H * ((2 - β₁) / (3 / 2 : ℝ)) ^ m := by
            rw [div_pow (2 - β₁) (3 / 2 : ℝ)]; ring
        _ ≤ M_H * (5 / 6 : ℝ) ^ m := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) hrat m) hM_nn
    have hgeom : Summable (fun k : ℕ => M_H * (5 / 6 : ℝ) ^ N * (5 / 6 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have htsum_geom : ∑' k : ℕ, M_H * (5 / 6 : ℝ) ^ N * (5 / 6 : ℝ) ^ k = 6 * M_H * (5 / 6 : ℝ) ^ N := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num; ring
    have habs_le : ‖∑' k : ℕ, (cauchyPowerSeries H 2 (3 / 2 : ℝ) (k + N) (fun _ => (β₁ : ℂ) - 2)).re‖ ≤
        ∑' k : ℕ, M_H * (5 / 6 : ℝ) ^ N * (5 / 6 : ℝ) ^ k := by
      refine (norm_tsum_le_tsum_norm (hgeom.of_norm_bounded fun k => ?_)).trans ?_
      · simpa [Real.norm_eq_abs, pow_add, mul_assoc, mul_comm ((5 / 6 : ℝ) ^ N)] using hnorm_term (k + N)
      · exact Summable.tsum_le_tsum (fun k => by
            simpa [pow_add, mul_assoc, mul_comm ((5 / 6 : ℝ) ^ N)] using hnorm_term (k + N))
          (hgeom.of_norm_bounded fun k => by
            simpa [Real.norm_eq_abs, pow_add, mul_assoc, mul_comm ((5 / 6 : ℝ) ^ N)] using hnorm_term (k + N))
          hgeom
    simpa [Real.norm_eq_abs, htsum_geom] using habs_le
  -- Sum the lower bound over `k ∈ Finset.range N`!
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hM1 : 1 ≤ M_H := by
      have h1 : (1 : ℝ) ≤ (q₁ : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast NeZero.pos q₁)
      have h2 : (1 : ℝ) ≤ (q₂ : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast NeZero.pos q₂)
      dsimp only [M_H]; nlinarith
    have hpos_r : 0 ≤ lam * (2 - β₁) ^ 0 / (1 - β₁) := by
      have : 0 < 1 - β₁ := by linarith
      positivity
    linarith [show (5 / 6 : ℝ) ^ 0 = 1 by norm_num]
  · have hpart_ge :
        1 - lam * ((2 - β₁) ^ N - 1) / (1 - β₁) ≤
          ∑ k ∈ Finset.range N, (cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2)).re := by
      have h1 : ∑ k ∈ Finset.range N, ((if k = 0 then (1 : ℝ) else 0) - lam * (2 - β₁) ^ k) ≤
          ∑ k ∈ Finset.range N, (cauchyPowerSeries H 2 (3 / 2 : ℝ) k (fun _ => (β₁ : ℂ) - 2)).re :=
        Finset.sum_le_sum fun k _ => hterm_lower k
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
      have h0sum : ∑ k ∈ Finset.range N, (if k = 0 then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => (1 : ℝ)), if_pos (Finset.mem_range.mpr hN)]
      have hgeom_N : ∑ k ∈ Finset.range N, (2 - β₁) ^ k = ((2 - β₁) ^ N - 1) / (1 - β₁) := by
        have hne : (2 - β₁ : ℝ) - 1 ≠ 0 := by linarith
        have := geom_sum_mul (2 - β₁) N
        have hsub : (2 - β₁ : ℝ) - 1 = 1 - β₁ := by ring
        rw [hsub] at this
        exact (eq_div_iff (by linarith)).mpr this
      rw [h0sum, hgeom_N] at h1
      linarith [show lam * (((2 - β₁) ^ N - 1) / (1 - β₁)) = lam * ((2 - β₁) ^ N - 1) / (1 - β₁) by ring]
    have htail_neg := (abs_le.mp htail_le).1
    have halg : lam / (1 - β₁) + lam * ((2 - β₁) ^ N - 1) / (1 - β₁) = lam * (2 - β₁) ^ N / (1 - β₁) := by
      field_simp [(by linarith : 1 - β₁ ≠ 0)]; ring
    linarith

/-- **UNCONDITIONAL SIEGEL'S THEOREM — REAL-ZERO EXCLUSION (`0` ASSUMPTIONS!)**:
for EVERY `ε > 0`, there exists `c > 0` such that for EVERY `q ≥ 1` (`[NeZero q]`),
EVERY real non-principal primitive character `χ : DirichletCharacter ℂ q`, and EVERY real `β : ℝ`:
`DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c / (q : ℝ) ^ ε`. -/
theorem siegel_theorem_real_zero_exclusion {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          β ≤ 1 - c / (q : ℝ) ^ ε := by
  set ε' : ℝ := min ε (1 / 4) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hε'_le_qtr : ε' ≤ 1 / 4 := min_le_right _ _
  set δ : ℝ := ε' / 48 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_small : δ < 1 / 16 := by dsimp only [δ]; linarith
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁),
      χ₁.IsPrimitive ∧ χ₁ ≠ 1 ∧ (∀ a : ZMod q₁, (χ₁ a).im = 0) ∧
      ∃ β₁ : ℝ, 1 - δ < β₁ ∧ DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0
  · -- Case 2: An exceptional character `(q₁, χ₁, β₁)` with `1 - δ < β₁ < 1` exists!
    obtain ⟨q₁, hnz₁, χ₁, hprim1, h1_ne, hreal1, β₁, hβ₁_gt, hz1⟩ := hex
    have hβ₁_lt1 : β₁ < 1 := by
      by_contra hge; push Not at hge
      exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ₁ (.inl h1_ne) (by simpa using hge) hz1
    have h1β₁_pos : 0 < 1 - β₁ := by linarith
    have h1β₁_lt : 1 - β₁ < δ := by linarith
    have hL1_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₁ h1_ne hreal1
    have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (NeZero.pos q₁)
    -- Choose constant `c_fin` covering BOTH `PChar.of χ₂ = PChar.of χ₁` and `PChar.of χ₂ ≠ PChar.of χ₁`!
    set C_exp : ℝ := Real.exp (δ * (6 * Real.log (180000 * (q₁ : ℝ) ^ 2) + 1)) with hC_exp_def
    have hC_exp_pos : 0 < C_exp := Real.exp_pos _
    set C_log : ℝ := 5 * (Real.log (2 * (q₁ : ℝ)) + 8 / ε') with hC_log_def
    have hC_log_pos : 0 < C_log := by
      have : 0 ≤ Real.log (2 * (q₁ : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast NeZero.pos q₁
        linarith)
      positivity
    set C_sq : ℝ := (16 / ε') ^ 2 with hC_sq_def
    have hC_sq_pos : 0 < C_sq := by positivity
    have hL1_re_pos : 0 < (DirichletCharacter.LFunction χ₁ 1).re := hL1_pos.1
    set c_other : ℝ :=
      (1 - β₁) / (2 * C_exp * (DirichletCharacter.LFunction χ₁ 1).re * C_log * (288 * C_sq))
    have hc_other_pos : 0 < c_other := by positivity
    set c_self : ℝ := (DirichletCharacter.LFunction χ₁ 1).re / (288 * (Real.log (2 * (q₁ : ℝ))) ^ 2)
    have hq₁2 : 2 ≤ q₁ := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one h1_ne
    have hlog2q₁_pos : 0 < Real.log (2 * (q₁ : ℝ)) := Real.log_pos (by
      have : (2 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁2
      linarith)
    have hc_self_pos : 0 < c_self := by positivity
    set c_fin : ℝ := min c_other c_self
    have hc_fin_pos : 0 < c_fin := lt_min hc_other_pos hc_self_pos
    refine ⟨c_fin, hc_fin_pos, fun q₂ _ χ₂ hprim2 h2_ne hreal2 β₂ hz2 => ?_⟩
    have hq₂2 : 2 ≤ q₂ := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one h2_ne
    have hq₂R : (2 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂2
    have hq₂_pos : (0 : ℝ) < (q₂ : ℝ) := by linarith
    have hq₂_ε : (q₂ : ℝ) ^ ε' ≤ (q₂ : ℝ) ^ ε :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hε'_le_ε
    by_cases hsame : PChar.of χ₁ = PChar.of χ₂
    · -- Same primitive character: `q₂ = q₁` and `LFunction χ₂ 1 = LFunction χ₁ 1`!
      have hψeq : (⟨q₁, χ₁, hprim1⟩ : PChar) = ⟨q₂, χ₂, hprim2⟩ := by
        rw [← PChar.of_self ⟨q₁, χ₁, hprim1⟩, ← PChar.of_self ⟨q₂, χ₂, hprim2⟩]
        exact hsame
      have hqeq : q₁ = q₂ := congrArg PChar.N hψeq
      have hL1_eq : (DirichletCharacter.LFunction χ₁ 1).re = (DirichletCharacter.LFunction χ₂ 1).re := by
        exact congrArg (fun ψ : PChar => (DirichletCharacter.LFunction ψ.χ 1).re) hψeq
      have hlandau : c_self ≤ 1 - β₂ := by
        have h := Stage7SiegelWalfisz.one_sub_zero_ge_LFunction_one_div h2_ne hz2
        have hEq : c_self = (DirichletCharacter.LFunction χ₂ 1).re / (288 * (Real.log (2 * (q₂ : ℝ))) ^ 2) := by
          dsimp only [c_self]; rw [hL1_eq, hqeq]
        linarith
      have hq₂_ge1 : (1 : ℝ) ≤ (q₂ : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
      have hdiv : c_fin / (q₂ : ℝ) ^ ε ≤ c_self := by
        calc c_fin / (q₂ : ℝ) ^ ε ≤ c_fin / 1 := div_le_div_of_nonneg_left hc_fin_pos.le zero_lt_one hq₂_ge1
          _ = c_fin := div_one _
          _ ≤ c_self := min_le_right _ _
      linarith
    · -- Distinct primitive character: apply `estermann_key_inequality`!
      set χ₁₂ := Stage3ZeroFreeRegion.prodChar χ₁ χ₂
      have hreal12 : ∀ a : ZMod (q₁ * q₂), (χ₁₂ a).im = 0 := by
        intro a
        rw [← ZMod.natCast_zmod_val a, Stage3ZeroFreeRegion.prodChar_apply_nat]
        simp [Complex.mul_im, hreal1, hreal2]
      set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
      set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
      have hψ_ne : ψ₁ ≠ ψ₂ := fun h => hsame (by rw [show PChar.of χ₁ = ψ₁ from PChar.of_self ψ₁,
        show PChar.of χ₂ = ψ₂ from PChar.of_self ψ₂, h])
      have h12_ne : χ₁₂ ≠ 1 :=
        Stage3ZeroFreeRegion.prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
      have hL2_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₂ h2_ne hreal2
      have hL12_pos := Stage6ClassNumberFormula.LFunction_one_pos_of_real χ₁₂ h12_ne hreal12
      set M_H : ℝ := 15000 * (q₁ : ℝ) ^ 2 * (q₂ : ℝ) ^ 2
      have hM_ge1 : 1 ≤ M_H := by
        have h1 : (1 : ℝ) ≤ (q₁ : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast NeZero.pos q₁)
        have h2 : (1 : ℝ) ≤ (q₂ : ℝ) ^ 2 := one_le_pow₀ (by linarith)
        dsimp only [M_H]; nlinarith
      have hlog65_gt : (1 / 6 : ℝ) < Real.log (6 / 5 : ℝ) := by
        have hpow : Real.exp 1 < (6 / 5 : ℝ) ^ 6 := by
          have : (6 / 5 : ℝ) ^ 6 = 46656 / 15625 := by norm_num
          linarith [Real.exp_one_lt_d9]
        have hlog := Real.log_lt_log (Real.exp_pos 1) hpow
        rw [Real.log_exp, Real.log_pow] at hlog
        push_cast at hlog; linarith
      set N : ℕ := ⌈Real.log (12 * M_H) / Real.log (6 / 5 : ℝ)⌉₊
      have hN_ge : Real.log (12 * M_H) / Real.log (6 / 5 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
      have hN_le : (N : ℝ) ≤ 6 * Real.log (12 * M_H) + 1 := by
        have hnn : 0 ≤ Real.log (12 * M_H) / Real.log (6 / 5 : ℝ) :=
          div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        have hlt := Nat.ceil_lt_add_one hnn
        have hdiv : Real.log (12 * M_H) / Real.log (6 / 5 : ℝ) ≤ 6 * Real.log (12 * M_H) := by
          rw [div_le_iff₀ (by linarith : 0 < Real.log (6 / 5 : ℝ))]
          nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 12 * M_H)]
        linarith
      have htail_half : 6 * M_H * (5 / 6 : ℝ) ^ N ≤ 1 / 2 := by
        have hlog_ge : Real.log (12 * M_H) ≤ (N : ℝ) * Real.log (6 / 5 : ℝ) :=
          (div_le_iff₀ (by linarith : 0 < Real.log (6 / 5 : ℝ))).mp hN_ge
        have hpow_ge : 12 * M_H ≤ (6 / 5 : ℝ) ^ N := by
          have := Real.exp_le_exp.mpr hlog_ge
          rw [Real.exp_log (by linarith), ← Real.log_pow, Real.exp_log (by positivity)] at this
          exact this
        have hinv : (5 / 6 : ℝ) ^ N = ((6 / 5 : ℝ) ^ N)⁻¹ := by
          rw [← inv_pow]; norm_num
        rw [hinv, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        linarith
      have hest := estermann_key_inequality hprim1 hprim2 h1_ne h2_ne hreal1 hreal2 hsame
        (by linarith) hβ₁_lt1 hz1 N
      have hhalf_le : (1 / 2 : ℝ) ≤
          ((DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
            (DirichletCharacter.LFunction χ₁₂ 1).re) * (2 - β₁) ^ N / (1 - β₁) := by linarith
      -- Bound `(2 - β₁) ^ N ≤ C_exp * q₂ ^ (ε' / 4)`!
      have h2β_pow : (2 - β₁) ^ N ≤ C_exp * (q₂ : ℝ) ^ (ε' / 4) := by
        have h1 : 2 - β₁ ≤ Real.exp δ := by
          have := Real.add_one_le_exp δ; linarith
        have h2 : (2 - β₁) ^ N ≤ Real.exp (δ * (N : ℝ)) := by
          calc (2 - β₁) ^ N ≤ (Real.exp δ) ^ N := pow_le_pow_left₀ (by linarith) h1 N
            _ = Real.exp ((N : ℝ) * δ) := (Real.exp_nat_mul δ N).symm
            _ = Real.exp (δ * (N : ℝ)) := by ring_nf
        have hlog12 : Real.log (12 * M_H) = Real.log (180000 * (q₁ : ℝ) ^ 2) + 2 * Real.log (q₂ : ℝ) := by
          have hEq : 12 * M_H = (180000 * (q₁ : ℝ) ^ 2) * (q₂ : ℝ) ^ 2 := by dsimp only [M_H]; ring
          rw [hEq, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
        have hδN : δ * (N : ℝ) ≤ δ * (6 * Real.log (180000 * (q₁ : ℝ) ^ 2) + 1) + (ε' / 4) * Real.log (q₂ : ℝ) := by
          have h12δ : 12 * δ = ε' / 4 := by dsimp only [δ]; ring
          have := mul_le_mul_of_nonneg_left hN_le hδ_pos.le
          rw [hlog12] at this
          have hexpand : δ * (6 * (Real.log (180000 * (q₁ : ℝ) ^ 2) + 2 * Real.log (q₂ : ℝ)) + 1) =
              δ * (6 * Real.log (180000 * (q₁ : ℝ) ^ 2) + 1) + (12 * δ) * Real.log (q₂ : ℝ) := by ring
          rw [hexpand, h12δ] at this
          exact this
        calc (2 - β₁) ^ N ≤ Real.exp (δ * (N : ℝ)) := h2
          _ ≤ Real.exp (δ * (6 * Real.log (180000 * (q₁ : ℝ) ^ 2) + 1) + (ε' / 4) * Real.log (q₂ : ℝ)) :=
              Real.exp_le_exp.mpr hδN
          _ = C_exp * (q₂ : ℝ) ^ (ε' / 4) := by
              rw [Real.exp_add, Real.rpow_def_of_pos hq₂_pos]; dsimp only [C_exp]; ring_nf
      -- Bound `(LFunction χ₁₂ 1).re ≤ C_log * q₂ ^ (ε' / 8)`!
      have hL12_le : (DirichletCharacter.LFunction χ₁₂ 1).re ≤ C_log * (q₂ : ℝ) ^ (ε' / 8) := by
        have hbd := Stage5DirichletLZeroFree.norm_LFunction_le_log_of_one_le_re h12_ne (s := 1) (by simp) (by simp)
        simp only [Complex.one_im, abs_zero, zero_add] at hbd
        have hlog_split : Real.log (((q₁ * q₂ : ℕ) : ℝ) * 2) = Real.log (2 * (q₁ : ℝ)) + Real.log (q₂ : ℝ) := by
          push_cast
          rw [show (q₁ : ℝ) * (q₂ : ℝ) * 2 = (2 * (q₁ : ℝ)) * (q₂ : ℝ) by ring,
            Real.log_mul (by positivity) hq₂_pos.ne']
        have hlogq₂ : Real.log (q₂ : ℝ) ≤ (8 / ε') * (q₂ : ℝ) ^ (ε' / 8) := by
          have h := Real.log_le_rpow_div hq₂_pos.le (show 0 < ε' / 8 by positivity)
          linarith [show (q₂ : ℝ) ^ (ε' / 8) / (ε' / 8) = (8 / ε') * (q₂ : ℝ) ^ (ε' / 8) by field_simp [hε'_pos.ne']]
        have hq2_ge1 : (1 : ℝ) ≤ (q₂ : ℝ) ^ (ε' / 8) := Real.one_le_rpow (by linarith) (by positivity)
        have hlog2q1_nn : 0 ≤ Real.log (2 * (q₁ : ℝ)) := Real.log_nonneg (by
          have : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast NeZero.pos q₁
          linarith)
        calc (DirichletCharacter.LFunction χ₁₂ 1).re
            ≤ ‖DirichletCharacter.LFunction χ₁₂ 1‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ 5 * Real.log (((q₁ * q₂ : ℕ) : ℝ) * 2) := hbd
          _ = 5 * (Real.log (2 * (q₁ : ℝ)) + Real.log (q₂ : ℝ)) := by rw [hlog_split]
          _ ≤ 5 * (Real.log (2 * (q₁ : ℝ)) * (q₂ : ℝ) ^ (ε' / 8) + (8 / ε') * (q₂ : ℝ) ^ (ε' / 8)) := by
              nlinarith
          _ = C_log * (q₂ : ℝ) ^ (ε' / 8) := by dsimp only [C_log]; ring
      -- Bound `(Real.log (2 * q₂)) ^ 2 ≤ C_sq * q₂ ^ (ε' / 4)`!
      have hlog2q2_sq : (Real.log (2 * (q₂ : ℝ))) ^ 2 ≤ C_sq * (q₂ : ℝ) ^ (ε' / 4) := by
        have h1 : Real.log (2 * (q₂ : ℝ)) ≤ 2 * Real.log (q₂ : ℝ) := by
          have h2q : 2 * (q₂ : ℝ) ≤ (q₂ : ℝ) ^ 2 := by nlinarith
          calc Real.log (2 * (q₂ : ℝ)) ≤ Real.log ((q₂ : ℝ) ^ 2) := Real.log_le_log (by positivity) h2q
            _ = 2 * Real.log (q₂ : ℝ) := by rw [Real.log_pow]; push_cast; ring
        have h2 : Real.log (q₂ : ℝ) ≤ (8 / ε') * (q₂ : ℝ) ^ (ε' / 8) := by
          have h := Real.log_le_rpow_div hq₂_pos.le (show 0 < ε' / 8 by positivity)
          linarith [show (q₂ : ℝ) ^ (ε' / 8) / (ε' / 8) = (8 / ε') * (q₂ : ℝ) ^ (ε' / 8) by field_simp [hε'_pos.ne']]
        have h3 : Real.log (2 * (q₂ : ℝ)) ≤ (16 / ε') * (q₂ : ℝ) ^ (ε' / 8) := by
          linarith [show 2 * ((8 / ε') * (q₂ : ℝ) ^ (ε' / 8)) = (16 / ε') * (q₂ : ℝ) ^ (ε' / 8) by ring]
        have hsq := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h3 2
        rw [mul_pow, ← Real.rpow_natCast ((q₂ : ℝ) ^ (ε' / 8)) 2, ← Real.rpow_mul hq₂_pos.le] at hsq
        have hexp : ε' / 8 * ((2 : ℕ) : ℝ) = ε' / 4 := by push_cast; ring
        rwa [hexp] at hsq
      -- Combine to get `(LFunction χ₂ 1).re ≥ ...` and apply Landau's `one_sub_zero_ge_LFunction_one_div`!
      have hL2_ge : (1 - β₁) / (2 * C_exp * (DirichletCharacter.LFunction χ₁ 1).re * C_log) *
          (q₂ : ℝ) ^ (-(3 * ε' / 8)) ≤ (DirichletCharacter.LFunction χ₂ 1).re := by
        have hmul1 :
            ((DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              (DirichletCharacter.LFunction χ₁₂ 1).re) * (2 - β₁) ^ N ≤
            (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              (C_log * (q₂ : ℝ) ^ (ε' / 8)) * (C_exp * (q₂ : ℝ) ^ (ε' / 4)) := by
          have hpos_a : 0 ≤ (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re :=
            mul_nonneg hL1_pos.1.le hL2_pos.1.le
          have h12_mul :
              (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
                (DirichletCharacter.LFunction χ₁₂ 1).re ≤
              (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
                (C_log * (q₂ : ℝ) ^ (ε' / 8)) :=
            mul_le_mul_of_nonneg_left hL12_le hpos_a
          exact mul_le_mul h12_mul h2β_pow (pow_nonneg (by linarith) N) (by positivity)
        have hpow_add : (q₂ : ℝ) ^ (ε' / 8) * (q₂ : ℝ) ^ (ε' / 4) = (q₂ : ℝ) ^ (3 * ε' / 8) := by
          rw [← Real.rpow_add hq₂_pos]; congr 1; ring
        have hhalf2 : (1 - β₁) / 2 ≤
            (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              C_log * C_exp * (q₂ : ℝ) ^ (3 * ε' / 8) := by
          have h1 := (le_div_iff₀ h1β₁_pos).mp hhalf_le
          have h2 : (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              (C_log * (q₂ : ℝ) ^ (ε' / 8)) * (C_exp * (q₂ : ℝ) ^ (ε' / 4)) =
            (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
              C_log * C_exp * (q₂ : ℝ) ^ (3 * ε' / 8) := by rw [← hpow_add]; ring
          linarith
        have hpow_pos : 0 < (q₂ : ℝ) ^ (3 * ε' / 8) := Real.rpow_pos_of_pos hq₂_pos _
        have hden_pos : 0 < 2 * C_exp * (DirichletCharacter.LFunction χ₁ 1).re * C_log * (q₂ : ℝ) ^ (3 * ε' / 8) := by
          positivity
        rw [Real.rpow_neg hq₂_pos.le, ← div_eq_mul_inv, div_div, div_le_iff₀ hden_pos]
        linarith
      have hlandau := Stage7SiegelWalfisz.one_sub_zero_ge_LFunction_one_div h2_ne hz2
      have hq2_pow_le : (q₂ : ℝ) ^ (5 * ε' / 8) ≤ (q₂ : ℝ) ^ ε :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hden_le : 288 * (Real.log (2 * (q₂ : ℝ))) ^ 2 ≤ 288 * C_sq * (q₂ : ℝ) ^ (ε' / 4) := by linarith
      have hlog2q2_pos : 0 < Real.log (2 * (q₂ : ℝ)) := Real.log_pos (by linarith)
      have h1β₂_ge : c_other / (q₂ : ℝ) ^ (5 * ε' / 8) ≤ 1 - β₂ := by
        have hpow_comb : (q₂ : ℝ) ^ (3 * ε' / 8) * (q₂ : ℝ) ^ (ε' / 4) = (q₂ : ℝ) ^ (5 * ε' / 8) := by
          rw [← Real.rpow_add hq₂_pos]; congr 1; ring
        have hstep1 :
            ((1 - β₁) / (2 * C_exp * (DirichletCharacter.LFunction χ₁ 1).re * C_log) *
              (q₂ : ℝ) ^ (-(3 * ε' / 8))) / (288 * C_sq * (q₂ : ℝ) ^ (ε' / 4)) ≤
            (DirichletCharacter.LFunction χ₂ 1).re / (288 * (Real.log (2 * (q₂ : ℝ))) ^ 2) :=
          div_le_div₀ hL2_pos.1.le hL2_ge (by positivity) hden_le
        have hlhs_eq :
            ((1 - β₁) / (2 * C_exp * (DirichletCharacter.LFunction χ₁ 1).re * C_log) *
              (q₂ : ℝ) ^ (-(3 * ε' / 8))) / (288 * C_sq * (q₂ : ℝ) ^ (ε' / 4)) =
            c_other / (q₂ : ℝ) ^ (5 * ε' / 8) := by
          rw [Real.rpow_neg hq₂_pos.le, ← hpow_comb]
          dsimp only [c_other]
          field_simp [hC_exp_pos.ne', hL1_pos.1.ne', hC_log_pos.ne', hC_sq_pos.ne',
            (Real.rpow_pos_of_pos hq₂_pos (3 * ε' / 8)).ne', (Real.rpow_pos_of_pos hq₂_pos (ε' / 4)).ne']
        linarith
      have hdiv_fin : c_fin / (q₂ : ℝ) ^ ε ≤ c_other / (q₂ : ℝ) ^ (5 * ε' / 8) := by
        calc c_fin / (q₂ : ℝ) ^ ε ≤ c_other / (q₂ : ℝ) ^ ε :=
              div_le_div_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hq₂_pos.le _)
          _ ≤ c_other / (q₂ : ℝ) ^ (5 * ε' / 8) :=
              div_le_div_of_nonneg_left hc_other_pos.le (Real.rpow_pos_of_pos hq₂_pos _) hq2_pow_le
      linarith
  · -- Case 1: No real primitive character has a real zero in `(1 - δ, 1)`!
    push Not at hex
    refine ⟨δ, hδ_pos, fun q _ χ hprim hχ hreal β hz => ?_⟩
    have hβ_le : β ≤ 1 - δ := by
      by_contra hgt; push Not at hgt
      exact hex q inferInstance χ hprim hχ hreal β hgt hz
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast NeZero.pos q) hε.le
    have hdiv : δ / (q : ℝ) ^ ε ≤ δ := div_le_self hδ_pos.le hq_ge1
    linarith

/-! ## Section 3: Unconditional Uniform Siegel–Walfisz Theorem (`0` Assumptions!) -/

/-- **UNCONDITIONAL UNIFORM ZERO-FREE REGION FOR ALL PRIMITIVE DIRICHLET CHARACTERS (`0` ASSUMPTIONS!)**:
for EVERY `ε > 0`, there exists `c > 0` such that for ALL `d ≥ 1` (`[NeZero d]`),
ALL primitive non-principal `χ : DirichletCharacter ℂ d`, and ALL `s : ℂ`:
`1 - c / max ((Real.log (d * (|s.im| + 2))) ^ 9) (d ^ ε) ≤ s.re → LFunction χ s ≠ 0`. -/
theorem siegel_walfisz_zeroFreeRegion {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
        χ.IsPrimitive → χ ≠ 1 →
        ∀ s : ℂ,
          1 - c / max ((Real.log ((d : ℝ) * (|s.im| + 2))) ^ 9) ((d : ℝ) ^ ε) ≤ s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c_S, hc_S, hSiegel⟩ := siegel_theorem_real_zero_exclusion hε
  obtain ⟨c_low, hc_low, hLow⟩ := LFunction_real_char_zeroFree_low_nonreal
  set c : ℝ := min (min Stage5DirichletLZeroFree.zeroFreeConst (c_S / 2)) c_low with hc_def
  have hc_pos : 0 < c := lt_min (lt_min Stage5DirichletLZeroFree.zeroFreeConst_pos (by positivity)) hc_low
  refine ⟨c, hc_pos, fun d _ χ hprim hχ s hs => ?_⟩
  have hd2 : 2 ≤ d := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  set L : ℝ := Real.log ((d : ℝ) * (|s.im| + 2)) with hL_def
  have hL_gt1 : 1 < L := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have h4 : (4 : ℝ) ≤ (d : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  have hL9_pos : 0 < L ^ 9 := pow_pos hL_pos 9
  have hdε_pos : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hd_pos ε
  set M : ℝ := max (L ^ 9) ((d : ℝ) ^ ε) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le hL9_pos (le_max_left _ _)
  by_cases hcase : χ ^ 2 ≠ 1 ∨ 1 ≤ |s.im|
  · -- Complex character or `|s.im| ≥ 1`: Stage 5 uniform zero-free region!
    have hdiv : c / M ≤ Stage5DirichletLZeroFree.zeroFreeConst / L ^ 9 := by
      calc c / M ≤ Stage5DirichletLZeroFree.zeroFreeConst / M :=
            div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hM_pos.le
        _ ≤ Stage5DirichletLZeroFree.zeroFreeConst / L ^ 9 :=
            div_le_div_of_nonneg_left Stage5DirichletLZeroFree.zeroFreeConst_pos.le hL9_pos (le_max_left _ _)
    exact Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion hχ hcase (by linarith)
  · -- Real primitive character (`χ ^ 2 = 1`) and low height (`|s.im| < 1`)!
    push Not at hcase
    obtain ⟨hsq1, him_lt1⟩ := hcase
    have hreal : ∀ a : ZMod d, (χ a).im = 0 := by
      intro a
      have hsq : (χ a) ^ 2 = (χ ^ 2) a := by simp [sq, MulChar.mul_apply]
      rw [hsq1] at hsq
      by_cases hu : IsUnit a
      · rw [MulChar.one_apply hu] at hsq
        rcases sq_eq_one_iff.mp hsq with h1 | h1 <;> simp [h1]
      · rw [MulChar.map_nonunit _ hu]; simp
    by_cases him0 : s.im = 0
    · -- Real point `s = (s.re : ℂ)`: apply unconditional Siegel's Theorem!
      intro hzero
      have hs_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him0])
      rw [hs_eq] at hzero
      have hβ_le := hSiegel d χ hprim hχ hreal s.re hzero
      have hdiv : c / M ≤ (c_S / 2) / (d : ℝ) ^ ε := by
        calc c / M ≤ (c_S / 2) / M :=
              div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hM_pos.le
          _ ≤ (c_S / 2) / (d : ℝ) ^ ε :=
              div_le_div_of_nonneg_left (by positivity) hdε_pos (le_max_right _ _)
      have hstrict : (c_S / 2) / (d : ℝ) ^ ε < c_S / (d : ℝ) ^ ε :=
        div_lt_div_of_pos_right (by linarith) hdε_pos
      linarith
    · -- Non-real low point `0 < |s.im| < 1`: apply `LFunction_real_char_zeroFree_low_nonreal`!
      have hlog2d_pos : 0 < Real.log (2 * (d : ℝ)) := Real.log_pos (by linarith)
      have hlog2d_le_L : Real.log (2 * (d : ℝ)) ≤ L :=
        Real.log_le_log (by positivity) (by nlinarith [abs_nonneg s.im])
      have hL_le_L9 : L ≤ L ^ 9 := by
        have h1 : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL_gt1.le
        nlinarith
      have hdiv : c / M ≤ c_low / Real.log (2 * (d : ℝ)) := by
        calc c / M ≤ c_low / M := div_le_div_of_nonneg_right (min_le_right _ _) hM_pos.le
          _ ≤ c_low / L ^ 9 := div_le_div_of_nonneg_left hc_low.le hL9_pos (le_max_left _ _)
          _ ≤ c_low / Real.log (2 * (d : ℝ)) :=
              div_le_div_of_nonneg_left hc_low.le hlog2d_pos (hlog2d_le_L.trans hL_le_L9)
      exact hLow d χ hχ hreal s him0 him_lt1.le (by linarith)

/-- **Uniform Rectangle Log-Derivative Bound via Borel–Carathéodory**:
for any `χ ≠ 1` mod `d`, `T ≥ 2`, and `0 < η ≤ 1 / 32`, if `LFunction χ z ≠ 0` whenever
`1 - 4 * η ≤ z.re` and `|z.im| ≤ T + 1`, then for EVERY `s : ℂ` with
`1 - η / 2 ≤ s.re ≤ 2` and `|s.im| ≤ T`:
`‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ (8 / η) * Real.log (8 * d * (T + 3) / η) + 2 / η + 1`. -/
theorem negLogDerivL_uniform_rect_bound {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ ≠ 1) {T η : ℝ} (hT : 2 ≤ T) (hη0 : 0 < η) (hη : η ≤ 1 / 32)
    (hzf : ∀ z : ℂ, 1 - 4 * η ≤ z.re → |z.im| ≤ T + 1 → DirichletCharacter.LFunction χ z ≠ 0) :
    ∀ s : ℂ, 1 - η / 2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        (8 / η) * Real.log (8 * (d : ℝ) * (T + 3) / η) + 2 / η + 1 := by
  have hd2 : 2 ≤ d := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have harg_gt1 : 1 < 8 * (d : ℝ) * (T + 3) / η := by
    rw [one_lt_div hη0]; nlinarith
  have hM_pos : 0 < Real.log (8 * (d : ℝ) * (T + 3) / η) := Real.log_pos harg_gt1
  intro s hs_lo hs_hi hs_im
  set t : ℝ := s.im
  by_cases hright : 1 + η / 2 ≤ s.re
  · -- Right sub-strip: `s.re ≥ 1 + η / 2`
    have hs_re_gt1 : 1 < s.re := by linarith
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s; simpa only [t, mul_comm I] using this
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_re_gt1 t).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv_le : 1 / (s.re - 1) ≤ 2 / η := by
      rw [div_le_div_iff₀ (by linarith) hη0]; linarith
    have hpos1 : 0 ≤ (8 / η) * Real.log (8 * (d : ℝ) * (T + 3) / η) := by positivity
    linarith
  · -- Critical strip `1 - η / 2 ≤ s.re < 1 + η / 2`: Borel–Carathéodory on disk centered at `(1 + η) + i t`
    push Not at hright
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ)
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im : |z.im| ≤ T + 1 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le1 : R_open ≤ 1 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      exact hzf z (by dsimp only [R_open] at hre_diff; linarith) hz_im
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    set M : ℝ := Real.log (8 * (d : ℝ) * (T + 3) / η)
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
      have hR_le : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_hi : |z.im| ≤ T + 1 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 2 * (d : ℝ) * (T + 3) := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg d)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (d : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ (d : ℝ) * (2 + (T + 1)) / (1 / 2) :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hd_pos.le)
                (by norm_num) hz_re_lo
          _ = 2 * (d : ℝ) * (T + 3) := by ring
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 2 / η := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) t).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        exact h.trans (div_le_div_of_nonneg_right (by linarith) hη0.le)
      have hratio_le : ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
          8 * (d : ℝ) * (T + 3) / η := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
              DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
          norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (2 * (d : ℝ) * (T + 3)) * (2 / η) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = 4 * (d : ℝ) * (T + 3) / η := by ring
          _ ≤ 8 * (d : ℝ) * (T + 3) / η := by
              refine div_le_div_of_nonneg_right (by nlinarith) hη0.le
      have hre_eq : (Log z).re =
          Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        have hexp : Real.exp (Log z).re =
            ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      rw [hre_eq]
      exact Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)) hratio_le
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      dsimp only [r]; constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 2 / η := by
      dsimp only [R, r]; field_simp [hη0.ne']; ring
    rw [hcoeff] at hbc
    have hneg_norm :
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    have h2le8 : (2 / η) * M ≤ (8 / η) * M := by
      have h1 : 2 / η ≤ 8 / η := div_le_div_of_nonneg_right (by norm_num) hη0.le
      exact mul_le_mul_of_nonneg_right h1 hM_pos.le
    have hpos_tail : 0 ≤ 2 / η + 1 := by positivity
    linarith

/-- Elementary exponential decay inequality: `u ^ k * exp (-(k : ℝ) * u) ≤ 1` for `k : ℕ`, `u ≥ 0`. -/
private lemma pow_mul_exp_neg_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-(k : ℝ) * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ k * Real.exp (-(k : ℝ) * u) = (u * Real.exp (-u)) ^ k := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
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
  · have hpow : (Real.log x) ^ p ≤ (Real.log x) ^ q := Real.rpow_le_rpow_of_exponent_le hL1 hpq
    have hexp1 : Real.exp (-c * (Real.log x) ^ q) ≤ Real.exp (-c * (Real.log x) ^ p) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h1 : (1 : ℝ) ≤ Real.exp c := Real.one_le_exp hc.le
    nlinarith [Real.exp_pos (-c * (Real.log x) ^ p)]
  · push Not at hL1
    have hpow_le1 : (Real.log x) ^ p ≤ 1 := Real.rpow_le_one hLx_pos.le hL1.le hp.le
    have hpow_nn : 0 ≤ (Real.log x) ^ q := Real.rpow_nonneg hLx_pos.le q
    have h1 : Real.exp (-c * (Real.log x) ^ q) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-c) ≤ Real.exp (-c * (Real.log x) ^ p) := Real.exp_le_exp.mpr (by nlinarith)
    have hcancel : Real.exp c * Real.exp (-c) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 1 ≤ Real.exp c * Real.exp (-c * (Real.log x) ^ p) := by
      rw [← hcancel]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le
    linarith

/-- **UNCONDITIONAL UNIFORM SIEGEL–WALFISZ BOUND FOR `ψ₁(x, χ)` (`0` ASSUMPTIONS!)**:
for EVERY `B > 0`, there exists `C > 0` such that for ALL `x ≥ 4`, ALL `d ≥ 1` (`[NeZero d]`)
with `(d : ℝ) ≤ (Real.log x) ^ B`, and ALL primitive non-principal `χ : DirichletCharacter ℂ d`:
`‖psi1Char χ x‖ ≤ C * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem siegel_walfisz_psi1Char {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
        χ.IsPrimitive → χ ≠ 1 → (d : ℝ) ≤ (Real.log x) ^ B →
        ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          C * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ)) := by
  set ε : ℝ := 1 / (40 * B) with hε_def
  have hε_pos : 0 < ε := by positivity
  obtain ⟨c_zf, hc_zf, hzf⟩ := siegel_walfisz_zeroFreeRegion hε_pos
  set c_star : ℝ := min c_zf (1 / 4) with hc_star_def
  have hc_star_pos : 0 < c_star := lt_min hc_zf (by norm_num)
  have hc_star_le_zf : c_star ≤ c_zf := min_le_left _ _
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  set K_B : ℝ := (20 * B + 3) ^ (9 : ℕ) with hKB_def
  have hKB_ge : (19683 : ℝ) ≤ K_B := by
    have h1 : (3 : ℝ) ≤ 20 * B + 3 := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h1 9
    norm_num at h2; exact h2
  have hKB_pos : 0 < K_B := by linarith
  -- Log-derivative constant `C_nd` so `M_nd ≤ C_nd * Lx` for all `u ≥ 2`
  set C_const : ℝ := max 0 (Real.log (32 * K_B / c_star)) with hC_const_def
  have hC_const_nn : 0 ≤ C_const := le_max_left _ _
  set C_nd : ℝ := (32 * K_B / c_star) * (C_const + 20 * B + 12) + 8 * K_B / c_star + 1 with hC_nd_def
  have hC_nd_pos : 0 < C_nd := by positivity
  -- Threshold `u₀ ≥ 2` so `u ^ 10 ≥ 8 * K_B / c_star` for all `u ≥ u₀`
  set u₀ : ℝ := max 2 (8 * K_B / c_star + 1) with hu₀_def
  have hu₀_ge2 : 2 ≤ u₀ := le_max_left _ _
  set x₀ : ℝ := max 4 (Real.exp (u₀ ^ (20 : ℕ))) with hx₀_def
  have hx₀_ge4 : 4 ≤ x₀ := le_max_left _ _
  set K_large : ℝ := (48 / Real.pi + 5 * C_nd / Real.pi) * (40 : ℝ) ^ (20 : ℕ) with hK_large_def
  have hK_large_pos : 0 < K_large := by positivity
  -- Step 1: Uniform contour shift for all `x ≥ x₀`
  have hlarge : ∀ x : ℝ, x₀ ≤ x → ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ.IsPrimitive → χ ≠ 1 → (d : ℝ) ≤ (Real.log x) ^ B →
      ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        K_large * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ)) := by
    intro x hx d _ χ hprim hχ hdB
    have hx4 : 4 ≤ x := hx₀_ge4.trans hx
    have hx0 : 0 < x := by linarith
    have hd2 : 2 ≤ d := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_u₀20 : u₀ ^ (20 : ℕ) ≤ Lx := by
      have h1 : Real.exp (u₀ ^ (20 : ℕ)) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) h1)
    have hLx_pos : 0 < Lx := lt_of_lt_of_le (pow_pos (by linarith : 0 < u₀) 20) hLx_ge_u₀20
    set u : ℝ := Lx ^ (1 / 20 : ℝ) with hu_def
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
    have hu_pow20 : u ^ (20 : ℕ) = Lx := by
      dsimp only [u]; rw [← Real.rpow_natCast, ← Real.rpow_mul hLx_pos.le]; norm_num
    have hu_ge_u₀ : u₀ ≤ u := by
      by_contra hlt; push Not at hlt
      have hpow : u ^ (20 : ℕ) < u₀ ^ (20 : ℕ) := pow_lt_pow_left₀ hlt hu_pos.le (by norm_num)
      linarith
    have hu_ge2 : 2 ≤ u := hu₀_ge2.trans hu_ge_u₀
    have hu_ge1 : 1 ≤ u := by linarith
    set T : ℝ := Real.exp u with hT_def
    have hT_pos : 0 < T := Real.exp_pos u
    have hT_ge4 : 4 ≤ T := by
      have h1 : Real.exp 2 ≤ T := Real.exp_le_exp.mpr hu_ge2
      have h2 : (4 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        nlinarith
      linarith
    have hT_ge2 : 2 ≤ T := by linarith
    set η : ℝ := c_star / (4 * K_B * u ^ (9 : ℕ)) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      have hu9 : (1 : ℝ) ≤ u ^ (9 : ℕ) := one_le_pow₀ hu_ge1
      dsimp only [η]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    -- Key log bound: `Real.log (d * (T + 3)) ≤ (20 * B + 3) * u`
    have hlog_dT3 : Real.log ((d : ℝ) * (T + 3)) ≤ (20 * B + 3) * u := by
      have hT3_le : T + 3 ≤ 4 * T := by linarith
      have hlogd : Real.log (d : ℝ) ≤ 20 * B * u := by
        have h1 : Real.log (d : ℝ) ≤ Real.log (Lx ^ B) := Real.log_le_log hd_pos hdB
        rw [Real.log_rpow hLx_pos, ← hu_pow20, Real.log_pow] at h1
        have hlogu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
        push_cast at h1; nlinarith
      have hlog4 : Real.log 4 ≤ 2 * u := by
        have h1 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      calc Real.log ((d : ℝ) * (T + 3))
          ≤ Real.log ((d : ℝ) * (4 * T)) :=
            Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hT3_le hd_pos.le)
        _ = Real.log (d : ℝ) + Real.log 4 + Real.log T := by
            rw [Real.log_mul hd_pos.ne' (by positivity), Real.log_mul (by norm_num) hT_pos.ne', add_assoc]
        _ = Real.log (d : ℝ) + Real.log 4 + u := by rw [hT_def, Real.log_exp]
        _ ≤ 20 * B * u + 2 * u + u := by linarith
        _ = (20 * B + 3) * u := by ring
    -- Key `d ^ ε` bound: `(d : ℝ) ^ ε ≤ K_B * u ^ 9`
    have hdε_le : (d : ℝ) ^ ε ≤ K_B * u ^ (9 : ℕ) := by
      have h1 : (d : ℝ) ^ ε ≤ (Lx ^ B) ^ ε := Real.rpow_le_rpow hd_pos.le hdB hε_pos.le
      rw [← Real.rpow_mul hLx_pos.le, ← hu_pow20, ← Real.rpow_natCast u 20,
        ← Real.rpow_mul hu_pos.le] at h1
      have hexp : ((20 : ℕ) : ℝ) * (B * ε) = 1 / 2 := by
        dsimp only [ε]; push_cast; field_simp [hB.ne']; ring
      rw [hexp] at h1
      have hu_half : u ^ (1 / 2 : ℝ) ≤ u ^ (9 : ℕ) := by
        rw [← Real.rpow_natCast u 9]
        exact Real.rpow_le_rpow_of_exponent_le hu_ge1 (by norm_num)
      have hu9_nn : 0 ≤ u ^ (9 : ℕ) := by positivity
      nlinarith
    -- Zero-freeness on `1 - 4 * η ≤ z.re ∧ |z.im| ≤ T + 1`
    have hzf_strip : ∀ z : ℂ, 1 - 4 * η ≤ z.re → |z.im| ≤ T + 1 →
        DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz_re hz_im
      have hlogz : Real.log ((d : ℝ) * (|z.im| + 2)) ≤ (20 * B + 3) * u := by
        have h1 : Real.log ((d : ℝ) * (|z.im| + 2)) ≤ Real.log ((d : ℝ) * (T + 3)) :=
          Real.log_le_log (by nlinarith [abs_nonneg z.im]) (by nlinarith [abs_nonneg z.im])
        exact h1.trans hlog_dT3
      have hlogz_nn : 0 ≤ Real.log ((d : ℝ) * (|z.im| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg z.im])
      have hpow9 : (Real.log ((d : ℝ) * (|z.im| + 2))) ^ (9 : ℕ) ≤ K_B * u ^ (9 : ℕ) := by
        have h1 := pow_le_pow_left₀ hlogz_nn hlogz 9
        rwa [mul_pow] at h1
      have hmax_le : max ((Real.log ((d : ℝ) * (|z.im| + 2))) ^ 9) ((d : ℝ) ^ ε) ≤ K_B * u ^ (9 : ℕ) :=
        max_le hpow9 hdε_le
      have hmax_pos : 0 < max ((Real.log ((d : ℝ) * (|z.im| + 2))) ^ 9) ((d : ℝ) ^ ε) :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos hd_pos ε) (le_max_right _ _)
      have h4η_le : 4 * η ≤ c_zf / max ((Real.log ((d : ℝ) * (|z.im| + 2))) ^ 9) ((d : ℝ) ^ ε) := by
        have h4η_eq : 4 * η = c_star / (K_B * u ^ (9 : ℕ)) := by
          dsimp only [η]; field_simp [hKB_pos.ne', hu_pos.ne']
        rw [h4η_eq]
        calc c_star / (K_B * u ^ (9 : ℕ))
            ≤ c_star / max ((Real.log ((d : ℝ) * (|z.im| + 2))) ^ 9) ((d : ℝ) ^ ε) :=
              div_le_div_of_nonneg_left hc_star_pos.le hmax_pos hmax_le
          _ ≤ c_zf / max ((Real.log ((d : ℝ) * (|z.im| + 2))) ^ 9) ((d : ℝ) ^ ε) :=
              div_le_div_of_nonneg_right hc_star_le_zf hmax_pos.le
      exact hzf d χ hprim hχ z (by linarith)
    -- Uniform log-derivative bound `≤ C_nd * Lx` on `[1 - η/2, 2] × [-T, T]`!
    have hnd_rect : ∀ s : ℂ, 1 - η / 2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ C_nd * Lx := by
      intro s hs_lo hs_hi hs_im
      have hbd := negLogDerivL_uniform_rect_bound hχ hT_ge2 hη_pos hη_le hzf_strip s hs_lo hs_hi hs_im
      have hlog_M : Real.log (8 * (d : ℝ) * (T + 3) / η) ≤ (C_const + 20 * B + 12) * u := by
        have hEq : 8 * (d : ℝ) * (T + 3) / η =
            (32 * K_B / c_star) * ((d : ℝ) * (T + 3)) * u ^ (9 : ℕ) := by
          dsimp only [η]; field_simp [hc_star_pos.ne', hKB_pos.ne', hu_pos.ne']; ring
        rw [hEq, Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
        have h1 : Real.log (32 * K_B / c_star) ≤ C_const := le_max_right _ _
        have h2 : C_const ≤ C_const * u := by nlinarith
        have h3 : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
        push_cast; linarith
      have hu9_le : u ^ (9 : ℕ) ≤ u ^ (10 : ℕ) := by nlinarith [pow_pos hu_pos 9]
      have hu10_le_Lx : u ^ (10 : ℕ) ≤ Lx := by
        rw [← hu_pow20, show u ^ (20 : ℕ) = u ^ (10 : ℕ) * u ^ (10 : ℕ) by ring]
        have h1 : (1 : ℝ) ≤ u ^ (10 : ℕ) := one_le_pow₀ hu_ge1
        nlinarith [pow_pos hu_pos 10]
      have h1_le_u10 : (1 : ℝ) ≤ u ^ (10 : ℕ) := one_le_pow₀ hu_ge1
      have hterm1 : (8 / η) * Real.log (8 * (d : ℝ) * (T + 3) / η) ≤
          (32 * K_B / c_star) * (C_const + 20 * B + 12) * u ^ (10 : ℕ) := by
        have h8 : 8 / η = (32 * K_B / c_star) * u ^ (9 : ℕ) := by
          dsimp only [η]; field_simp [hc_star_pos.ne', hKB_pos.ne', hu_pos.ne']; ring
        rw [h8]
        calc (32 * K_B / c_star) * u ^ (9 : ℕ) * Real.log (8 * (d : ℝ) * (T + 3) / η)
            ≤ (32 * K_B / c_star) * u ^ (9 : ℕ) * ((C_const + 20 * B + 12) * u) :=
              mul_le_mul_of_nonneg_left hlog_M (by positivity)
          _ = (32 * K_B / c_star) * (C_const + 20 * B + 12) * u ^ (10 : ℕ) := by ring
      have hterm2 : 2 / η ≤ (8 * K_B / c_star) * u ^ (10 : ℕ) := by
        have h2 : 2 / η = (8 * K_B / c_star) * u ^ (9 : ℕ) := by
          dsimp only [η]; field_simp [hc_star_pos.ne', hKB_pos.ne', hu_pos.ne']; ring
        rw [h2]; exact mul_le_mul_of_nonneg_left hu9_le (by positivity)
      calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
          ≤ (8 / η) * Real.log (8 * (d : ℝ) * (T + 3) / η) + 2 / η + 1 := hbd
        _ ≤ ((32 * K_B / c_star) * (C_const + 20 * B + 12) + 8 * K_B / c_star + 1) * u ^ (10 : ℕ) := by
            linarith
        _ = C_nd * u ^ (10 : ℕ) := by dsimp only [C_nd]
        _ ≤ C_nd * Lx := mul_le_mul_of_nonneg_left hu10_le_Lx hC_nd_pos.le
    -- Contour parameters `c` and `σ_T`
    set c : ℝ := 1 + 1 / (2 * Lx) with hc_def
    have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (by linarith : 0 < 2 * Lx)]
    have hc_le2 : c ≤ 2 := by
      have h1 : (1 : ℝ) ≤ 2 * Lx := by
        have : (1 : ℝ) ≤ u ^ (20 : ℕ) := one_le_pow₀ hu_ge1
        linarith
      have : 1 / (2 * Lx) ≤ 1 := (div_le_one (by linarith)).mpr h1
      dsimp only [c]; linarith
    have hx_pow_c : x ^ (c + 1) ≤ 2 * x ^ 2 := by
      have h1 : x ^ (c + 1) = x ^ 2 * x ^ (1 / (2 * Lx)) := by
        rw [show c + 1 = (2 : ℝ) + 1 / (2 * Lx) by dsimp only [c]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (1 / (2 * Lx)) = Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; field_simp [hLx_pos.ne']
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]
      rw [h1, h2]; nlinarith [sq_nonneg x]
    set σ_T : ℝ := 1 - η / 2 with hσ_def
    have hσ_ge_half : 1 / 2 ≤ σ_T := by dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    have hσ_lt_c : σ_T < c := by dsimp only [σ_T]; linarith
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    -- (A) Truncation error
    have htrunc_err :
        ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    -- (B) Exact pole-free contour shift identity
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        DirichletCharacter.LFunction χ z ≠ 0 := fun z hlo _ him =>
      hzf_strip z (by dsimp only [σ_T] at hlo; linarith) (by linarith)
    have hshift := Stage7PNTInAP.perron_contour_shift_psi1Char hχ hx0 hσ_pos hσ_lt_c hT_pos hzf_rect
    -- (C) Horizontal segment bounds
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ v in σ_T..c, F ((v : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C_nd * Lx * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C_nd * Lx * x ^ (c + 1) / T ^ 2) fun v hv => ?_).trans ?_
      · rw [Set.uIoc_of_le hσ_lt_c.le] at hv
        set z : ℂ := (v : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = v := by simp [z]
        have hz_abs_im : |z.im| = T := by
          simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
            add_zero, zero_add, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hnd := hnd_rect z (by rw [hz_re]; linarith [hv.1]) (by rw [hz_re]; linarith [hv.2])
          (by rw [hz_abs_im])
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = v + 1 := by simp [hz_re]
          rw [hre1]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hv.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by simpa [hz_abs_im] using Complex.abs_im_le_norm (z + 1)
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul]
        exact div_le_div₀ (by positivity)
          (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
          (sq_pos_of_pos hT_pos) hden_ge
      · rw [abs_of_nonneg (sub_nonneg.mpr hσ_lt_c.le)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C_nd * Lx * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C_nd * Lx * x ^ (c + 1) / T ^ 2 * 2 := mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C_nd * Lx * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C_nd * Lx * x ^ (c + 1) / T ^ 2 := by simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C_nd * Lx * x ^ (c + 1) / T ^ 2 := by simpa using hhoriz_bd (-1) (by norm_num)
    -- (D) Left vertical segment bound
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
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C_nd * Lx * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hnd' := hnd_rect z (by rw [hz_re]) (by rw [hz_re]; linarith) (by rw [hz_im]; exact htT)
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
      have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
        have h2 : |t| ≤ ‖z + 1‖ := by simpa [hz_im] using Complex.abs_im_le_norm (z + 1)
        have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
        rw [hsq]; exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
      have ht2_pos : 0 < t ^ 2 := by
        have : t ≠ 0 := fun h => by rw [h, abs_zero] at ht1; linarith
        positivity
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul, hpow]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _))
        ht2_pos hden
    have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      linarith [inv_nonneg.mpr hT_pos.le]
    have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht; rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.2] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      simp only [inv_neg, neg_neg, inv_one]; linarith [inv_nonneg.mpr hT_pos.le]
    have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C_nd * Lx * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C_nd * Lx * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C_nd * Lx * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C_nd * Lx * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C_nd * Lx * x ^ (σ_T + 1) * 1 := mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C_nd * Lx * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C_nd * Lx * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C_nd * Lx * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C_nd * Lx * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C_nd * Lx * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C_nd * Lx * x ^ (σ_T + 1) * 1 := mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C_nd * Lx * x ^ (σ_T + 1) := mul_one _
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * C_nd * Lx * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * C_nd * Lx * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have htT : |t| ≤ T := (abs_le.mpr ⟨ht.1.le, ht.2⟩).trans (by linarith)
        have hnd' := hnd_rect z (by rw [hz_re]) (by rw [hz_re]; linarith) (by simp [z]; exact htT)
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
            ≤ (C_nd * Lx) * x ^ (σ_T + 1) / (1 / 2) :=
              div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _)) (by norm_num) hden
          _ = 2 * C_nd * Lx * x ^ (σ_T + 1) := by ring
      · norm_num; linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        6 * C_nd * Lx * x ^ (σ_T + 1) := by
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
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (3 * C_nd / Real.pi) * Lx * x ^ (σ_T + 1) +
          (2 * C_nd / Real.pi) * Lx * x ^ 2 / T := by
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
          (3 * C_nd / Real.pi) * Lx * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (6 * C_nd * Lx * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (3 * C_nd / Real.pi) * Lx * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]; ring
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C_nd * Lx * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C_nd / Real.pi) * Lx * x ^ 2 / T := by
        intro Ival hIval
        have hxc_div : x ^ (c + 1) / T ^ 2 ≤ x ^ 2 / T := by
          have h1 : x ^ (c + 1) / T ^ 2 ≤ (2 * x ^ 2) / T ^ 2 :=
            div_le_div_of_nonneg_right hx_pow_c (sq_nonneg T)
          have h2 : 2 * x ^ 2 / T ^ 2 ≤ x ^ 2 / T := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
            have hT2 : 2 * T ≤ T ^ 2 := by
              rw [sq]; exact mul_le_mul_of_nonneg_right hT_ge2 hT_pos.le
            have hm := mul_le_mul_of_nonneg_left hT2 (sq_nonneg x)
            linarith only [hm]
          linarith only [h1, h2]
        calc (2 * Real.pi)⁻¹ * ‖Ival‖
            ≤ (2 * Real.pi)⁻¹ * (2 * C_nd * Lx * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C_nd / Real.pi) * Lx * (x ^ (c + 1) / T ^ 2) := by
              field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C_nd / Real.pi) * Lx * (x ^ 2 / T) :=
              mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C_nd / Real.pi) * Lx * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C_nd / Real.pi) * Lx * x ^ 2 / T + (C_nd / Real.pi) * Lx * x ^ 2 / T =
          (2 * C_nd / Real.pi) * Lx * x ^ 2 / T := by ring
      linarith only [htri, hterm_left, htop_h, hbot_h, hsum2]
    -- (F) Show `x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-u)` and absorb `Lx = u ^ 20`!
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-u) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(η / 2)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(η / 2)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(η / 2)) = Real.exp (-((η / 2) * Lx)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hge_u : u ≤ (η / 2) * Lx := by
        have hEq : (η / 2) * Lx = (c_star / (8 * K_B)) * u ^ (10 : ℕ) * u := by
          rw [← hu_pow20]; dsimp only [η]; field_simp [hKB_pos.ne', hu_pos.ne']; ring
        rw [hEq]
        have hu10_ge_u : u ≤ u ^ (10 : ℕ) := by
          calc u = 1 * u := (one_mul u).symm
            _ ≤ u ^ (9 : ℕ) * u := mul_le_mul_of_nonneg_right (one_le_pow₀ hu_ge1) hu_pos.le
            _ = u ^ (10 : ℕ) := by ring
        have hu_ge_ratio : 8 * K_B / c_star ≤ u := by
          have h1 : 8 * K_B / c_star + 1 ≤ u₀ := le_max_right _ _
          linarith only [h1, hu_ge_u₀]
        have hcoeff_ge1 : 1 ≤ (c_star / (8 * K_B)) * u ^ (10 : ℕ) := by
          have h1 : 8 * K_B / c_star ≤ u ^ (10 : ℕ) := hu_ge_ratio.trans hu10_ge_u
          have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c_star / (8 * K_B) by positivity)
          have hcancel : (c_star / (8 * K_B)) * (8 * K_B / c_star) = 1 := by
            field_simp [hc_star_pos.ne', hKB_pos.ne']
          linarith only [h2, hcancel]
        exact (one_mul u).symm.trans_le (mul_le_mul_of_nonneg_right hcoeff_ge1 hu_pos.le)
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hge_u)) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-u) := by rw [hT_def, one_div, Real.exp_neg]
    have habsorb : Lx * Real.exp (-u) ≤ (40 : ℝ) ^ (20 : ℕ) * Real.exp (-(1 / 2 : ℝ) * u) := by
      have hsplit : Real.exp (-u) =
          Real.exp (-((20 : ℕ) : ℝ) * (u / 40)) * Real.exp (-(1 / 2 : ℝ) * u) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have h1 : Lx = (40 : ℝ) ^ (20 : ℕ) * (u / 40) ^ (20 : ℕ) := by
        rw [← mul_pow, show (40 : ℝ) * (u / 40) = u by ring, hu_pow20]
      calc Lx * Real.exp (-((20 : ℕ) : ℝ) * (u / 40))
          = (40 : ℝ) ^ (20 : ℕ) * ((u / 40) ^ (20 : ℕ) * Real.exp (-((20 : ℕ) : ℝ) * (u / 40))) := by
            rw [h1, mul_assoc]
        _ ≤ (40 : ℝ) ^ (20 : ℕ) * 1 :=
            mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one 20 (by positivity)) (by positivity)
        _ = (40 : ℝ) ^ (20 : ℕ) := mul_one _
    have htri_tot : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ +
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
        (Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
    have ht1 : (48 / Real.pi) * x ^ 2 * Lx / T = (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have ht2 : (3 * C_nd / Real.pi) * Lx * x ^ (σ_T + 1) ≤
        (3 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by
      calc (3 * C_nd / Real.pi) * Lx * x ^ (σ_T + 1)
          ≤ (3 * C_nd / Real.pi) * Lx * (x ^ 2 * Real.exp (-u)) := by gcongr
        _ = (3 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by ring
    have ht3 : (2 * C_nd / Real.pi) * Lx * x ^ 2 / T =
        (2 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hsum3 :
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) +
        (3 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) +
        (2 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) =
        (48 / Real.pi + 5 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by ring
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ (48 / Real.pi + 5 * C_nd / Real.pi) * x ^ 2 * (Lx * Real.exp (-u)) := by
          linarith only [htri_tot, htrunc_err, hshift_bd, ht1, ht2, ht3, hsum3]
      _ ≤ (48 / Real.pi + 5 * C_nd / Real.pi) * x ^ 2 *
            ((40 : ℝ) ^ (20 : ℕ) * Real.exp (-(1 / 2 : ℝ) * u)) := by gcongr
      _ = K_large * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := by dsimp only [K_large]; ring
  -- Step 2: Cover `4 ≤ x < x₀` trivially via `‖psi1Char χ x‖ ≤ 6 * x ^ 2`
  set C_small : ℝ := 6 * Real.exp ((1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨C_fin, hC_fin_pos, fun x hx4 d _ χ hprim hχ hdB => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge d χ hprim hχ hdB).trans (by gcongr; exact le_max_left _ _)
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
            ≤ Λ n * 1 * x :=
              mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
                hmax (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
          _ = x * Λ n := by ring
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have hexp_ge :
        Real.exp (-(1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ)) ≤
          Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      have hrpow : (Real.log x) ^ (1 / 20 : ℝ) ≤ (Real.log x₀) ^ (1 / 20 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog (by norm_num)
      linarith
    have hcancel : C_small * Real.exp (-(1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ)) = 6 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : (1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ) +
          -(1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ 6 * x ^ 2 := hpsi1_le
      _ = C_small * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x₀) ^ (1 / 20 : ℝ)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ)) := by gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ (1 / 20 : ℝ)) := by
          gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL UNIFORM SIEGEL–WALFISZ CHARACTER-SUM DECAY (EXPONENTIAL FORM, `0` ASSUMPTIONS!)**:
for EVERY `B > 0`, there exist `c > 0` and `C > 0` such that for ALL `x ≥ 4`, ALL `d ≥ 1` (`[NeZero d]`)
with `(d : ℝ) ≤ (Real.log x) ^ B`, and ALL primitive non-principal `χ : DirichletCharacter ℂ d`:
`‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem siegel_walfisz_chebyshevPsiChar_exp {B : ℝ} (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
        χ.IsPrimitive → χ ≠ 1 → (d : ℝ) ≤ (Real.log x) ^ B →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨C₁, hC₁, hpsi1⟩ := siegel_walfisz_psi1Char hB
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (1 / 4 : ℝ) c_ψ with hc_fin_def
  have hc_fin_pos : 0 < c_fin := lt_min (by norm_num) hc_ψ
  have hc_fin_le1 : c_fin ≤ 1 / 4 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ * Real.exp c_fin
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx4 d _ χ hprim hχ hdB => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx2 : 2 ≤ x := by linarith
  set u : ℝ := (Real.log x) ^ (1 / 20 : ℝ) with hu_def
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_x : h ≤ x := by nlinarith
  have hxph_ge4 : 4 ≤ x + h := by linarith
  have hxph_ge2 : 2 ≤ x + h := by linarith
  have hxph_le2x : x + h ≤ 2 * x := by linarith
  have hdB_xh : (d : ℝ) ≤ (Real.log (x + h)) ^ B :=
    hdB.trans (Real.rpow_le_rpow hLx_pos.le (Real.log_le_log hx0 (by linarith)) hB.le)
  have hexp_E2 : Real.exp (-(1 / 2 : ℝ) * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; nlinarith
  have hexp_xh : Real.exp (-(1 / 2 : ℝ) * (Real.log (x + h)) ^ (1 / 20 : ℝ)) ≤ E ^ 2 := by
    have hrpow : u ≤ (Real.log (x + h)) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow hLx_pos.le (Real.log_le_log hx0 (by linarith)) (by norm_num)
    exact (Real.exp_le_exp.mpr (by linarith)).trans hexp_E2
  have hexp_psi : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp c_fin * E := by
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp (-c_fin * (Real.log x) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]; apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)]
    exact h1.trans (exp_neg_rpow_le_of_le (by norm_num) (by norm_num) hc_fin_pos hx2)
  have hexp_psi_xh : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ Real.exp c_fin * E := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    exact (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog])).trans hexp_psi
  have hdiff := Stage7PNTInAP.norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hx0.le hh_pos.le
  have hnorm_mul : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ + ‖Stage4ExplicitFormula.psi1Char χ x‖ +
        h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
    have h1 : ‖(h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x‖ +
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
      simpa [sub_sub_cancel] using norm_sub_le
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x)
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh_pos.le] at h1
    linarith [norm_sub_le (Stage4ExplicitFormula.psi1Char χ (x + h)) (Stage4ExplicitFormula.psi1Char χ x)]
  have hbd_xh : ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ ≤ 4 * C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖
        ≤ C₁ * (x + h) ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log (x + h)) ^ (1 / 20 : ℝ)) :=
          hpsi1 (x + h) hxph_ge4 d χ hprim hχ hdB_xh
      _ ≤ C₁ * (2 * x) ^ 2 * E ^ 2 := by
          have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * x ^ 2 * E ^ 2 := by ring
  have hbd_x : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ C₁ * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := hpsi1 x hx4 d χ hprim hχ hdB
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
    dsimp only [h] at h1 h2 h3 ⊢; linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ h * (C_fin * x * E) := by
    have hrhs1 : 5 * C₁ * x ^ 2 * E ^ 2 = h * (5 * C₁ * x * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * x * E) + h * ((1 + 3 * C_ψ * Real.exp c_fin) * x * E) =
        h * (C_fin * x * E) := by dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

/-- Helper: for any `c > 0`, `p > 0`, `A > 0`, there exists `C > 0` such that for all `x ≥ 4`,
`Real.exp (-c * (Real.log x) ^ p) ≤ C / (Real.log x) ^ A`. -/
private lemma exp_neg_rpow_log_le_div_log_rpow {c p A : ℝ} (hc : 0 < c) (hp : 0 < p) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x →
      Real.exp (-c * (Real.log x) ^ p) ≤ C / (Real.log x) ^ A := by
  set k : ℕ := ⌈A / p⌉₊ with hk_def
  have hk_pos : 0 < k := Nat.ceil_pos.mpr (div_pos hA hp)
  have hk_ge : A / p ≤ (k : ℝ) := Nat.le_ceil _
  have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  set C : ℝ := ((k : ℝ) / c) ^ k with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun x hx => ?_⟩
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
  set u : ℝ := (Real.log x) ^ p
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos p
  have hA_le : (Real.log x) ^ A ≤ u ^ k := by
    rw [← Real.rpow_natCast u k, show u ^ (k : ℝ) = (Real.log x) ^ (p * (k : ℝ)) by
      dsimp only [u]; rw [← Real.rpow_mul hLx_pos.le]]
    have hpk : A ≤ p * (k : ℝ) := (div_le_iff₀ hp).mp hk_ge |>.trans_eq (mul_comm _ _)
    exact Real.rpow_le_rpow_of_exponent_le hLx_ge1 hpk
  have huk_exp : u ^ k * Real.exp (-c * u) ≤ C := by
    have hEq : u ^ k * Real.exp (-c * u) =
        C * (((c / (k : ℝ)) * u) ^ k * Real.exp (-(k : ℝ) * ((c / (k : ℝ)) * u))) := by
      have h1 : (-(k : ℝ) * ((c / (k : ℝ)) * u)) = -c * u := by field_simp [hkR_pos.ne']
      have h2 : C * ((c / (k : ℝ)) * u) ^ k = u ^ k := by
        dsimp only [C]; rw [← mul_pow]
        congr 1; field_simp [hc.ne', hkR_pos.ne']
      rw [h1, ← mul_assoc, h2]
    rw [hEq]
    exact (mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one k (by positivity)) hC_pos.le).trans_eq (mul_one C)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A)]
  calc Real.exp (-c * u) * (Real.log x) ^ A
      ≤ Real.exp (-c * u) * u ^ k := mul_le_mul_of_nonneg_left hA_le (Real.exp_pos _).le
    _ = u ^ k * Real.exp (-c * u) := mul_comm _ _
    _ ≤ C := huk_exp

/-- **UNCONDITIONAL UNIFORM SIEGEL–WALFISZ CHARACTER-SUM THEOREM (`0` ASSUMPTIONS!)**:
for EVERY `A > 0` and `B > 0`, there exists `C > 0` such that for ALL `x ≥ 4`, ALL `d ≥ 1` (`[NeZero d]`)
with `(d : ℝ) ≤ (Real.log x) ^ B`, and ALL primitive non-principal `χ : DirichletCharacter ℂ d`:
`‖chebyshevPsiChar χ x‖ ≤ C * x / (Real.log x) ^ A`. -/
theorem siegel_walfisz_chebyshevPsiChar {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
        χ.IsPrimitive → χ ≠ 1 → (d : ℝ) ≤ (Real.log x) ^ B →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd⟩ := siegel_walfisz_chebyshevPsiChar_exp hB
  obtain ⟨C₂, hC₂, hexp⟩ := exp_neg_rpow_log_le_div_log_rpow hc₁ (by norm_num : (0 : ℝ) < 1 / 20) hA
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun x hx4 d _ χ hprim hχ hdB => ?_⟩
  calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
      ≤ C₁ * x * Real.exp (-c₁ * (Real.log x) ^ (1 / 20 : ℝ)) := hbd x hx4 d χ hprim hχ hdB
    _ ≤ C₁ * x * (C₂ / (Real.log x) ^ A) :=
        mul_le_mul_of_nonneg_left (hexp x hx4) (by positivity)
    _ = (C₁ * C₂) * x / (Real.log x) ^ A := by ring

/-- **UNCONDITIONAL SIEGEL–WALFISZ THEOREM FOR PRIMES IN ARITHMETIC PROGRESSIONS (`0` ASSUMPTIONS!)**:
for EVERY `A > 0` and `B > 0`, there exists `C > 0` such that for ALL `x ≥ 4`, ALL `q ≥ 1` (`[NeZero q]`)
with `(q : ℝ) ≤ (Real.log x) ^ B`, and ALL `a` with `Nat.Coprime a q`:
`|chebyshevPsiAP q a x - x / q.totient| ≤ C * x / (Real.log x) ^ A`. -/
theorem siegel_walfisz_psiAP {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ (q a : ℕ) [NeZero q],
        Nat.Coprime a q → (q : ℝ) ≤ (Real.log x) ^ B →
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          C * x / (Real.log x) ^ A := by
  obtain ⟨C_sw, hC_sw, hsw⟩ := siegel_walfisz_chebyshevPsiChar hA hB
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  obtain ⟨C_e, hC_e, hexp_psi⟩ := exp_neg_rpow_log_le_div_log_rpow hc_ψ (by norm_num : (0 : ℝ) < 1 / 2) hA
  -- Bound `(Real.log x) ^ (A + 2) ≤ C_pol * x` for `x ≥ 4` via `pow_mul_exp_neg_le_one`
  set k : ℕ := ⌈A + 2⌉₊ + 1
  have hk_pos : 0 < k := Nat.succ_pos _
  have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  set C_pol : ℝ := (k : ℝ) ^ k
  have hC_pol_pos : 0 < C_pol := by positivity
  have hlog_pow_le_x : ∀ x : ℝ, 4 ≤ x → (Real.log x) ^ (A + 2) ≤ C_pol * x := by
    intro x hx
    have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
      have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
    have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
    have hA2_le_k : A + 2 ≤ (k : ℝ) := by
      have h1 : A + 2 ≤ (⌈A + 2⌉₊ : ℝ) := Nat.le_ceil _
      dsimp only [k]; push_cast; linarith
    have h1 : (Real.log x) ^ (A + 2) ≤ (Real.log x) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hLx_ge1 hA2_le_k
    have h2 : (Real.log x) ^ k * Real.exp (-Real.log x) ≤ C_pol := by
      have hEq : (Real.log x) ^ k * Real.exp (-Real.log x) =
          C_pol * ((Real.log x / (k : ℝ)) ^ k * Real.exp (-(k : ℝ) * (Real.log x / (k : ℝ)))) := by
        have ha : -(k : ℝ) * (Real.log x / (k : ℝ)) = -Real.log x := by field_simp [hkR_pos.ne']
        have hb : C_pol * (Real.log x / (k : ℝ)) ^ k = (Real.log x) ^ k := by
          dsimp only [C_pol]; rw [← mul_pow]; congr 1; field_simp [hkR_pos.ne']
        rw [ha, ← mul_assoc, hb]
      rw [hEq]
      exact (mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one k (by positivity)) hC_pol_pos.le).trans_eq (mul_one _)
    rw [Real.exp_neg, Real.exp_log (by linarith : 0 < x), ← div_eq_mul_inv, div_le_iff₀ (by linarith)] at h2
    linarith
  set C_fin : ℝ := C_ψ * C_e + C_sw + 3 * (B + 1) * C_pol
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨C_fin, hC_fin_pos, fun x hx4 q a _ hcop hqB => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hE1 : |RHDirect.chebyshevPsi x - x| ≤ (C_ψ * C_e) * x / (Real.log x) ^ A := by
    have h1 := hpsi x (by linarith)
    have h2 := hexp_psi x hx4
    rw [Real.sqrt_eq_rpow] at h1
    calc |RHDirect.chebyshevPsi x - x|
        ≤ C_ψ * x * Real.exp (-c_ψ * (Real.log x) ^ (1 / 2 : ℝ)) := h1
      _ ≤ C_ψ * x * (C_e / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (C_ψ * C_e) * x / (Real.log x) ^ A := by ring
  have hlogq_le : Real.log (q : ℝ) ≤ B * Real.log x := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have h1 : Real.log (q : ℝ) ≤ Real.log ((Real.log x) ^ B) := Real.log_le_log hq_pos hqB
    rw [Real.log_rpow hLx_pos] at h1
    have h2 : Real.log (Real.log x) ≤ Real.log x := (Real.log_le_sub_one_of_pos hLx_pos).trans (by linarith)
    nlinarith
  have hlog2_le_x : (Real.log x) ^ 2 ≤ C_pol * x / (Real.log x) ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLx_pos A)]
    have hpow : (Real.log x) ^ 2 * (Real.log x) ^ A = (Real.log x) ^ (A + 2) := by
      rw [← Real.rpow_natCast (Real.log x) 2, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
    rw [hpow]; exact hlog_pow_le_x x hx4
  have hE2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ (C_sw + B * C_pol) * x / (Real.log x) ^ A := by
    intro χ hχ
    have hdiff := norm_chebyshevPsiChar_sub_primitive_le hχ hx1
    have hd_pos : 0 < χ.conductor := by
      have := three_le_conductor_of_ne_one hχ; omega
    have : NeZero χ.conductor := ⟨by omega⟩
    have hd_le_q : (χ.conductor : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    have hprim_ne : χ.primitiveCharacter ≠ 1 := by
      intro h1
      have hc1 : χ.conductor = 1 := by
        have := congrArg DirichletCharacter.conductor h1
        rw [χ.primitiveCharacter_isPrimitive, DirichletCharacter.conductor_one] at this
        exact this
      have := three_le_conductor_of_ne_one hχ; omega
    have hprim_bd := hsw x hx4 χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      hprim_ne (hd_le_q.trans hqB)
    have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ +
        ‖Stage2DirichletAP.chebyshevPsiChar χ x -
          Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ := by
      simpa [add_sub_cancel] using norm_add_le
        (Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
        (Stage2DirichletAP.chebyshevPsiChar χ x -
          Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
    have hlogq_x : Real.log (q : ℝ) * Real.log x ≤ B * C_pol * x / (Real.log x) ^ A := by
      calc Real.log (q : ℝ) * Real.log x
          ≤ (B * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right hlogq_le hLx_pos.le
        _ = B * (Real.log x) ^ 2 := by ring
        _ ≤ B * (C_pol * x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hlog2_le_x hB.le
        _ = B * C_pol * x / (Real.log x) ^ A := by ring
    have hsum : C_sw * x / (Real.log x) ^ A + B * C_pol * x / (Real.log x) ^ A =
        (C_sw + B * C_pol) * x / (Real.log x) ^ A := by ring
    linarith
  have hbase := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop hx1
    (by positivity) hE1 hE2
  have hcard_pf : (q.primeFactors.card : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    -- Direct proof: `2 ^ q.primeFactors.card ≤ q`, so `q.primeFactors.card * log 2 ≤ log q`
    have h2pow : 2 ^ q.primeFactors.card ≤ q := by
      calc 2 ^ q.primeFactors.card
          = ∏ _p ∈ q.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ q.primeFactors, p := Finset.prod_le_prod (fun _ _ => by omega)
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        _ ≤ q := Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
    have h2powR : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by exact_mod_cast h2pow
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog := Real.log_le_log (by positivity) h2powR
    rw [Real.log_pow] at hlog
    nlinarith [Nat.cast_nonneg (α := ℝ) q.primeFactors.card]
  have hpf_bd : (q.primeFactors.card : ℝ) * Real.log x ≤ 2 * B * C_pol * x / (Real.log x) ^ A := by
    calc (q.primeFactors.card : ℝ) * Real.log x
        ≤ (2 * Real.log (q : ℝ)) * Real.log x := mul_le_mul_of_nonneg_right hcard_pf hLx_pos.le
      _ ≤ (2 * (B * Real.log x)) * Real.log x := by nlinarith
      _ = 2 * B * (Real.log x) ^ 2 := by ring
      _ ≤ 2 * B * (C_pol * x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left hlog2_le_x (by positivity)
      _ = 2 * B * C_pol * x / (Real.log x) ^ A := by ring
  have hdiv_phi :
      ((C_ψ * C_e) * x / (Real.log x) ^ A + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
        (C_ψ * C_e) * x / (Real.log x) ^ A + 2 * B * C_pol * x / (Real.log x) ^ A := by
    have hnum_nn : 0 ≤ (C_ψ * C_e) * x / (Real.log x) ^ A + (q.primeFactors.card : ℝ) * Real.log x := by
      positivity
    exact (div_le_self hnum_nn hphi_ge1).trans (by linarith)
  have hB_le : 3 * B ≤ 3 * (B + 1) := by linarith
  have hcomb :
      (C_ψ * C_e) * x / (Real.log x) ^ A + 2 * B * C_pol * x / (Real.log x) ^ A +
        (C_sw + B * C_pol) * x / (Real.log x) ^ A ≤
      C_fin * x / (Real.log x) ^ A := by
    have hlhs :
        (C_ψ * C_e) * x / (Real.log x) ^ A + 2 * B * C_pol * x / (Real.log x) ^ A +
          (C_sw + B * C_pol) * x / (Real.log x) ^ A =
        (C_ψ * C_e + C_sw + 3 * B * C_pol) * x / (Real.log x) ^ A := by ring
    rw [hlhs]
    refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hLx_pos.le A)
    have : C_ψ * C_e + C_sw + 3 * B * C_pol ≤ C_fin := by dsimp only [C_fin]; nlinarith
    exact mul_le_mul_of_nonneg_right this hx0.le
  linarith

/-! ## Section 4: Unconditional Barban–Davenport–Halberstam Mean-Square Theorem (`0` Assumptions!) -/

/-- **UNCONDITIONAL BARBAN–DAVENPORT–HALBERSTAM MEAN-SQUARE THEOREM (`0` ASSUMPTIONS!)**:
for EVERY `A > 0`, there exists `C > 0` such that for ALL `x ≥ 4` and ALL `Q : ℕ` with `(Q : ℝ) ≤ x`:
`∑ q ∈ Finset.Icc 1 Q, ∑_{(a,q)=1} (ψ(x; q, a) - x / φ(q))² ≤ C * (x * Q * (Real.log x)³ + x² / (Real.log x)^A)`. -/
theorem barban_davenport_halberstam_full {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ Q : ℕ, (Q : ℝ) ≤ x →
        ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤
          C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
  classical
  set B : ℝ := A + 3 with hB_def
  have hB : 0 < B := by positivity
  set A' : ℝ := (A + B + 1) / 2 with hA'_def
  have hA' : 0 < A' := by positivity
  set A'' : ℝ := (A + 1) / 2 with hA''_def
  have hA'' : 0 < A'' := by positivity
  obtain ⟨C_sw, hC_sw, hsw⟩ := siegel_walfisz_chebyshevPsiChar hA' hB
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  obtain ⟨C_e, hC_e, hexp_psi⟩ :=
    exp_neg_rpow_log_le_div_log_rpow hc_ψ (by norm_num : (0 : ℝ) < 1 / 2) hA''
  set C_p : ℝ := C_ψ * C_e with hC_p_def
  have hC_p_pos : 0 < C_p := mul_pos hC_ψ hC_e
  set C_fin : ℝ := max (24 * 288 + 200) (48 * C_p ^ 2 + 48 * C_sw ^ 2 + 24 * 576) with hC_fin_def
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 24 * 288 + 200) (le_max_left _ _)
  refine ⟨C_fin, hC_fin_pos, fun x hx4 Q hQx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
  by_cases hQ0 : Q = 0
  · subst hQ0
    simp only [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty, Nat.cast_zero,
      mul_zero, zero_mul, zero_add]
    positivity
  · have hQ1 : 1 ≤ Q := by omega
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
    have htrans := ap_variance_Icc_le_principal_add_prim_sum hQ1 hx4 hQx
    -- 1. Principal term bound: `48 * |ψ(x) - x|² * log x ≤ 48 * C_p² * x² / (log x)^A`
    have hprinc_bd :
        48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x ≤
          48 * C_p ^ 2 * (x ^ 2 / (Real.log x) ^ A) := by
      have h1 : |RHDirect.chebyshevPsi x - x| ≤ C_p * x / (Real.log x) ^ A'' := by
        have hp := hpsi x (by linarith)
        rw [Real.sqrt_eq_rpow] at hp
        calc |RHDirect.chebyshevPsi x - x|
            ≤ C_ψ * x * Real.exp (-c_ψ * (Real.log x) ^ (1 / 2 : ℝ)) := hp
          _ ≤ C_ψ * x * (C_e / (Real.log x) ^ A'') :=
              mul_le_mul_of_nonneg_left (hexp_psi x hx4) (by positivity)
          _ = C_p * x / (Real.log x) ^ A'' := by dsimp only [C_p]; ring
      have hsq : |RHDirect.chebyshevPsi x - x| ^ 2 ≤
          C_p ^ 2 * x ^ 2 / (Real.log x) ^ (A + 1) := by
        have hs := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [div_pow, mul_pow, ← Real.rpow_natCast ((Real.log x) ^ A'') 2,
          ← Real.rpow_mul hLx_pos.le] at hs
        have hexp : A'' * ((2 : ℕ) : ℝ) = A + 1 := by dsimp only [A'']; push_cast; ring
        rwa [hexp] at hs
      have hpow_split : (Real.log x) ^ (A + 1) = (Real.log x) ^ A * Real.log x := by
        rw [Real.rpow_add hLx_pos, Real.rpow_one]
      calc 48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x
          ≤ 48 * (C_p ^ 2 * x ^ 2 / (Real.log x) ^ (A + 1)) * Real.log x := by gcongr
        _ = 48 * C_p ^ 2 * (x ^ 2 / (Real.log x) ^ A) := by
            rw [hpow_split]; field_simp [hLx_pos.ne', (Real.rpow_pos_of_pos hLx_pos A).ne']
    -- 2. Split primitive-conductor sum at `Q₁ := ⌊(Real.log x) ^ B⌋₊`
    set Q₁ : ℕ := ⌊(Real.log x) ^ B⌋₊ with hQ₁_def
    have hlogB_ge1 : (1 : ℝ) ≤ (Real.log x) ^ B := Real.one_le_rpow hLx_ge1 hB.le
    have hQ₁_ge1 : 1 ≤ Q₁ := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hlogB_ge1)
    have hQ₁_pos : (0 : ℝ) < (Q₁ : ℝ) := Nat.cast_pos.mpr hQ₁_ge1
    have hQ₁_le : (Q₁ : ℝ) ≤ (Real.log x) ^ B := Nat.floor_le (by positivity)
    have hQ₁_ge_half : (Real.log x) ^ B / 2 ≤ (Q₁ : ℝ) := by
      have hlt : (Real.log x) ^ B < (Q₁ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h1le : (1 : ℝ) ≤ (Q₁ : ℝ) := by exact_mod_cast hQ₁_ge1
      linarith
    set f : ℕ → ℝ := fun d =>
      (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
    have hsplit_sum :
        ∑ d ∈ Finset.Icc 2 Q, f d =
          ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁), f d +
          ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => ¬ d ≤ Q₁), f d :=
      (Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 Q) (fun d => d ≤ Q₁) f).symm
    -- 2a. Small conductors `d ≤ Q₁ ≤ (Real.log x) ^ B`: Siegel–Walfisz!
    have hsmall_bd :
        ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁), f d ≤
          2 * C_sw ^ 2 * (x ^ 2 / (Real.log x) ^ A) := by
      have hterm : ∀ d ∈ (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁),
          f d ≤ (2 * Real.log x) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) := by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd2, hdQ⟩, hdQ₁⟩ := hd
        have : NeZero d := ⟨by omega⟩
        have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
        have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
        have hlog_le : Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ 2 * Real.log x := by
          have hle : 2 * (Q : ℝ) / (d : ℝ) ≤ x ^ 2 := by
            calc 2 * (Q : ℝ) / (d : ℝ) ≤ 2 * (Q : ℝ) / 1 :=
                  div_le_div_of_nonneg_left (by positivity) zero_lt_one hdR
              _ = 2 * (Q : ℝ) := div_one _
              _ ≤ 2 * x := by linarith
              _ ≤ x ^ 2 := by nlinarith
          calc Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ Real.log (x ^ 2) :=
                Real.log_le_log (by positivity) hle
            _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
        have hsum_chi :
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
              (d.totient : ℝ) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) := by
          have hpt : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2 ≤
                C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A') := by
            intro χ hχ
            have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
            have hχne : χ ≠ 1 := by
              intro h1
              have hcond : d = 1 := by
                have hc : χ.conductor = d := hprim
                rw [h1, DirichletCharacter.conductor_one] at hc
                exact hc.symm
              omega
            have hdB : (d : ℝ) ≤ (Real.log x) ^ B :=
              (by exact_mod_cast hdQ₁ : (d : ℝ) ≤ (Q₁ : ℝ)).trans hQ₁_le
            have hbd := hsw x hx4 d χ hprim hχne hdB
            have hsq := pow_le_pow_left₀ (norm_nonneg _) hbd 2
            rw [div_pow, mul_pow, ← Real.rpow_natCast ((Real.log x) ^ A') 2,
              ← Real.rpow_mul hLx_pos.le] at hsq
            have hexp : A' * ((2 : ℕ) : ℝ) = 2 * A' := by push_cast; ring
            rwa [hexp] at hsq
          have hcard : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).card : ℝ) ≤
              (d.totient : ℝ) := by
            have htot : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
              rw [← Nat.card_eq_fintype_card]
              exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
            have hnat : (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).card ≤
                d.totient := by
              calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).card
                  ≤ (Finset.univ : Finset (DirichletCharacter ℂ d)).card := Finset.card_filter_le _ _
                _ = d.totient := by rw [Finset.card_univ, htot]
            exact_mod_cast hnat
          calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
              ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                  (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) := Finset.sum_le_sum hpt
            _ = ((Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).card : ℝ) *
                  (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (d.totient : ℝ) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
        have hlog_nn : 0 ≤ Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
          have hdQ' : (d : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hdQ
          have h1 : (1 : ℝ) ≤ 2 * (Q : ℝ) / (d : ℝ) := (one_le_div (by linarith)).mpr (by linarith)
          exact Real.log_nonneg h1
        dsimp only [f]
        calc (Real.log (2 * (Q : ℝ) / (d : ℝ)) / (d.totient : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
                  ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ^ 2
            ≤ ((2 * Real.log x) / (d.totient : ℝ)) *
                ((d.totient : ℝ) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A'))) :=
              mul_le_mul (div_le_div_of_nonneg_right hlog_le hphi_pos.le) hsum_chi
                (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
          _ = (2 * Real.log x) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A')) := by
              field_simp [hphi_pos.ne']
      have hcard_small : (((Finset.Icc 2 Q).filter (fun d => d ≤ Q₁)).card : ℝ) ≤ (Real.log x) ^ B := by
        have hsub : (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁) ⊆ Finset.Icc 1 Q₁ := fun d hd => by
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢; omega
        have hnat : ((Finset.Icc 2 Q).filter (fun d => d ≤ Q₁)).card ≤ Q₁ := by
          calc ((Finset.Icc 2 Q).filter (fun d => d ≤ Q₁)).card
              ≤ (Finset.Icc 1 Q₁).card := Finset.card_le_card hsub
            _ = Q₁ := by rw [Nat.card_Icc]; omega
        exact (by exact_mod_cast hnat : (((Finset.Icc 2 Q).filter (fun d => d ≤ Q₁)).card : ℝ) ≤ (Q₁ : ℝ)).trans hQ₁_le
      have hpow_comb : (Real.log x) ^ (2 * A') = (Real.log x) ^ A * (Real.log x) ^ B * Real.log x := by
        have hexp : 2 * A' = A + B + 1 := by dsimp only [A']; ring
        rw [hexp, Real.rpow_add hLx_pos, Real.rpow_add hLx_pos, Real.rpow_one]
      calc ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁), f d
          ≤ ∑ _d ∈ (Finset.Icc 2 Q).filter (fun d => d ≤ Q₁),
              ((2 * Real.log x) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A'))) :=
            Finset.sum_le_sum hterm
        _ = (((Finset.Icc 2 Q).filter (fun d => d ≤ Q₁)).card : ℝ) *
              ((2 * Real.log x) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A'))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Real.log x) ^ B * ((2 * Real.log x) * (C_sw ^ 2 * x ^ 2 / (Real.log x) ^ (2 * A'))) :=
            mul_le_mul_of_nonneg_right hcard_small (by positivity)
        _ = 2 * C_sw ^ 2 * (x ^ 2 / (Real.log x) ^ A) := by
            rw [hpow_comb]
            field_simp [hLx_pos.ne', (Real.rpow_pos_of_pos hLx_pos A).ne',
              (Real.rpow_pos_of_pos hLx_pos B).ne']
    -- 2b. Large conductors `d > Q₁`: Dyadic Large Sieve `prim_variance_Ioc_le`!
    have hlarge_bd :
        ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => ¬ d ≤ Q₁), f d ≤
          288 * x * (Q : ℝ) * (Real.log x) ^ 3 + 576 * (x ^ 2 / (Real.log x) ^ A) := by
      by_cases hQ₁Q : Q₁ ≤ Q
      · have hsub : (Finset.Icc 2 Q).filter (fun d => ¬ d ≤ Q₁) ⊆ Finset.Ioc Q₁ Q := fun d hd => by
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hd ⊢; omega
        have hf_nn : ∀ d ∈ Finset.Ioc Q₁ Q, 0 ≤ f d := fun d hd => by
          have hdQ : d ≤ Q := (Finset.mem_Ioc.mp hd).2
          have hd1 : 1 ≤ d := by have := (Finset.mem_Ioc.mp hd).1; omega
          have hlog_nn : 0 ≤ Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
            refine Real.log_nonneg ((one_le_div (by exact_mod_cast hd1 : (0 : ℝ) < (d : ℝ))).mpr ?_)
            have : (d : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hdQ
            linarith
          exact mul_nonneg (div_nonneg hlog_nn (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        have hls := prim_variance_Ioc_le hQ₁_ge1 hQ₁Q hx4 hQx
        have hterm2 : x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ) ≤ 2 * (x ^ 2 / (Real.log x) ^ A) := by
          have hpowB : (Real.log x) ^ B = (Real.log x) ^ A * (Real.log x) ^ 3 := by
            dsimp only [B]; rw [Real.rpow_add hLx_pos, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
          calc x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)
              ≤ x ^ 2 * (Real.log x) ^ 3 / ((Real.log x) ^ B / 2) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hQ₁_ge_half
            _ = 2 * (x ^ 2 / (Real.log x) ^ A) := by
                rw [hpowB]; field_simp [hLx_pos.ne', (Real.rpow_pos_of_pos hLx_pos A).ne']
        calc ∑ d ∈ (Finset.Icc 2 Q).filter (fun d => ¬ d ≤ Q₁), f d
            ≤ ∑ d ∈ Finset.Ioc Q₁ Q, f d := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => hf_nn d hd)
          _ ≤ 288 * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)) := hls
          _ ≤ 288 * x * (Q : ℝ) * (Real.log x) ^ 3 + 576 * (x ^ 2 / (Real.log x) ^ A) := by linarith
      · have hempty : (Finset.Icc 2 Q).filter (fun d => ¬ d ≤ Q₁) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro d hd; simp only [Finset.mem_Icc] at hd; omega
        rw [hempty, Finset.sum_empty]
        positivity
    -- 3. Combine everything!
    have hcoeff1 : (24 * 288 + 200 : ℝ) ≤ C_fin := le_max_left _ _
    have hcoeff2 : 48 * C_p ^ 2 + 48 * C_sw ^ 2 + 24 * 576 ≤ C_fin := le_max_right _ _
    have h1_nn : 0 ≤ x * (Q : ℝ) * (Real.log x) ^ 3 := by positivity
    have h2_nn : 0 ≤ x ^ 2 / (Real.log x) ^ A := by positivity
    have hcomb1 : (24 * 288 + 200 : ℝ) * (x * (Q : ℝ) * (Real.log x) ^ 3) ≤
        C_fin * (x * (Q : ℝ) * (Real.log x) ^ 3) := mul_le_mul_of_nonneg_right hcoeff1 h1_nn
    have hcomb2 : (48 * C_p ^ 2 + 48 * C_sw ^ 2 + 24 * 576) * (x ^ 2 / (Real.log x) ^ A) ≤
        C_fin * (x ^ 2 / (Real.log x) ^ A) := mul_le_mul_of_nonneg_right hcoeff2 h2_nn
    change ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤ _
    have htrans' : ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤
        48 * |RHDirect.chebyshevPsi x - x| ^ 2 * Real.log x +
        24 * (∑ d ∈ Finset.Icc 2 Q, f d) +
        200 * x * (Q : ℝ) * (Real.log x) ^ 3 := htrans
    rw [hsplit_sum] at htrans'
    linarith

/-- **Units-Form Barban–Davenport–Halberstam Theorem** (summing directly over `(ZMod (k + 1))ˣ`):
for EVERY `A > 0`, there exists `C > 0` such that for ALL `x ≥ 4` and ALL `Q : ℕ` with `(Q : ℝ) ≤ x`:
`∑ k ∈ Finset.range Q, ∑ a : (ZMod (k + 1))ˣ, (ψ(x; k + 1, a.val) - x / φ(k + 1))² ≤ C * (x * Q * (log x)³ + x² / (log x)^A)`. -/
theorem barban_davenport_halberstam_full_units {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ Q : ℕ, (Q : ℝ) ≤ x →
        ∑ k ∈ Finset.range Q, ∑ a : (ZMod (k + 1))ˣ,
            (Stage2DirichletAP.chebyshevPsiAP (k + 1) (a : ZMod (k + 1)).val x -
              x / ((k + 1).totient : ℝ)) ^ 2 ≤
          C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
  obtain ⟨C, hC, hbdh⟩ := barban_davenport_halberstam_full hA
  refine ⟨C, hC, fun x hx Q hQx => ?_⟩
  have heq :
      ∑ k ∈ Finset.range Q, ∑ a : (ZMod (k + 1))ˣ,
          (Stage2DirichletAP.chebyshevPsiAP (k + 1) (a : ZMod (k + 1)).val x -
            x / ((k + 1).totient : ℝ)) ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
    · intro _ _ _ _ h; omega
    · intro q hq; simp only [Finset.mem_Icc, Finset.mem_range] at hq ⊢; exact ⟨q - 1, by omega, by omega⟩
    · intro k _; exact (psiAPVariance_eq_units (q := k + 1) x).symm
  rw [heq]
  exact hbdh x hx Q hQx

/-- **UNCONDITIONAL SHARP BARBAN–DAVENPORT–HALBERSTAM THEOREM ON `x / (log x)^A ≤ Q ≤ x`**:
for EVERY `A > 0`, there exists `C > 0` such that for ALL `x ≥ 4` and ALL `Q : ℕ` with
`x / (Real.log x) ^ A ≤ (Q : ℝ)` and `(Q : ℝ) ≤ x`:
`∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤ C * (x * Q * (Real.log x) ^ 3)`. -/
theorem barban_davenport_halberstam_sharp {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ Q : ℕ, x / (Real.log x) ^ A ≤ (Q : ℝ) → (Q : ℝ) ≤ x →
        ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x ≤
          C * (x * (Q : ℝ) * (Real.log x) ^ 3) := by
  obtain ⟨C, hC, hbdh⟩ := barban_davenport_halberstam_full hA
  refine ⟨2 * C, by positivity, fun x hx Q hQlo hQhi => ?_⟩
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx3_ge1 : (1 : ℝ) ≤ (Real.log x) ^ 3 := one_le_pow₀ hLx_ge1
  have hx2_le : x ^ 2 / (Real.log x) ^ A ≤ x * (Q : ℝ) * (Real.log x) ^ 3 := by
    have h1 : x ^ 2 / (Real.log x) ^ A = x * (x / (Real.log x) ^ A) := by ring
    rw [h1]
    calc x * (x / (Real.log x) ^ A) ≤ x * (Q : ℝ) := mul_le_mul_of_nonneg_left hQlo (by linarith)
      _ ≤ x * (Q : ℝ) * (Real.log x) ^ 3 := by
          have hnn : 0 ≤ x * (Q : ℝ) := by positivity
          nlinarith
  calc ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x
      ≤ C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := hbdh x hx Q hQhi
    _ ≤ C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x * (Q : ℝ) * (Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = (2 * C) * (x * (Q : ℝ) * (Real.log x) ^ 3) := by ring

/-- **UNCONDITIONAL DYADIC BARBAN–DAVENPORT–HALBERSTAM THEOREM (`Finset.Ioc Q₁ Q`)**:
for EVERY `A > 0`, there exists `C > 0` such that for ALL `1 ≤ Q₁ ≤ Q` and `x ≥ 4` with
`(Q₁ : ℝ) ≤ (Real.log x) ^ A` and `(Q : ℝ) ≤ x`:
`∑ q ∈ Finset.Ioc Q₁ Q, psiAPVariance q x ≤ C * (x * Q * (Real.log x)³ + x² * (Real.log x)³ / Q₁)`. -/
theorem barban_davenport_halberstam_dyadic {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q₁ Q : ℕ, 1 ≤ Q₁ → Q₁ ≤ Q → ∀ x : ℝ, 4 ≤ x →
        (Q₁ : ℝ) ≤ (Real.log x) ^ A → (Q : ℝ) ≤ x →
        ∑ q ∈ Finset.Ioc Q₁ Q, psiAPVariance q x ≤
          C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)) := by
  obtain ⟨C, hC, hbdh⟩ := barban_davenport_halberstam_full hA
  refine ⟨C, hC, fun Q₁ Q hQ₁ _ x hx hQ₁A hQx => ?_⟩
  have hQ₁_pos : (0 : ℝ) < (Q₁ : ℝ) := Nat.cast_pos.mpr hQ₁
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx3_ge1 : (1 : ℝ) ≤ (Real.log x) ^ 3 := one_le_pow₀ hLx_ge1
  have hsub : Finset.Ioc Q₁ Q ⊆ Finset.Icc 1 Q := fun q hq => by
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hq ⊢; omega
  have hterm2 : x ^ 2 / (Real.log x) ^ A ≤ x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ) := by
    calc x ^ 2 / (Real.log x) ^ A
        ≤ x ^ 2 / (Q₁ : ℝ) := div_le_div_of_nonneg_left (sq_nonneg x) hQ₁_pos hQ₁A
      _ ≤ x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hQ₁_pos.le
          nlinarith [sq_nonneg x]
  calc ∑ q ∈ Finset.Ioc Q₁ Q, psiAPVariance q x
      ≤ ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => psiAPVariance_nonneg q x
    _ ≤ C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := hbdh x hx Q hQx
    _ ≤ C * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 * (Real.log x) ^ 3 / (Q₁ : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC.le

/-! ## Section 5: Average Bombieri–Vinogradov L¹ Corollary & Almost-All-Moduli PNT / Primes in AP -/

/-- **UNCONDITIONAL L¹ AVERAGE BOMBIERI–VINOGRADOV / BDH COROLLARY (CAUCHY–SCHWARZ)**:
for EVERY `A > 0`, there exists `C > 0` such that for ALL `x ≥ 4` and ALL `Q : ℕ` with `(Q : ℝ) ≤ x`:
`∑ q ∈ Finset.Icc 1 Q, ∑_{(a,q)=1} |ψ(x; q, a) - x / φ(q)| ≤ C * Q * √(x * Q * (log x)³ + x² / (log x)^A)`. -/
theorem barban_davenport_halberstam_L1_average {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ Q : ℕ, (Q : ℝ) ≤ x →
        ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          C * (Q : ℝ) * Real.sqrt (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := by
  obtain ⟨C₀, hC₀, hbdh⟩ := barban_davenport_halberstam_full hA
  refine ⟨Real.sqrt C₀, Real.sqrt_pos.mpr hC₀, fun x hx Q hQx => ?_⟩
  set S : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
  have hsum_eq :
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| =
        ∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| :=
    (Finset.sum_sigma (Finset.Icc 1 Q) (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
      (fun p => |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|)).symm
  have hsq_eq :
      ∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x := by
    simp only [sq_abs]
    exact Finset.sum_sigma _ _ _
  have hcard_le : (S.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hnat : S.card ≤ Q ^ 2 := by
      rw [Finset.card_sigma]
      calc ∑ q ∈ Finset.Icc 1 Q, ((Finset.range q).filter (fun a => Nat.Coprime a q)).card
          ≤ ∑ _q ∈ Finset.Icc 1 Q, Q := Finset.sum_le_sum fun q hq =>
            (Finset.card_filter_le _ _).trans (by rw [Finset.card_range]; exact (Finset.mem_Icc.mp hq).2)
        _ = (Finset.Icc 1 Q).card * Q := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Q * Q := by
            have hc : (Finset.Icc 1 Q).card ≤ Q := by rw [Nat.card_Icc]; omega
            exact Nat.mul_le_mul_right Q hc
        _ = Q ^ 2 := by ring
    exact_mod_cast hnat
  have hcs :
      (∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|) ^ 2 ≤
        (S.card : ℝ) * ∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| ^ 2 := by
    set g : (Σ _ : ℕ, ℕ) → ℝ := fun p =>
      |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|
    have h0 : 0 ≤ ∑ p ∈ S, ∑ r ∈ S, (g p - g r) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp :
        ∑ p ∈ S, ∑ r ∈ S, (g p - g r) ^ 2 =
          2 * ((S.card : ℝ) * ∑ p ∈ S, g p ^ 2 - (∑ p ∈ S, g p) ^ 2) := by
      have hterm : ∀ p ∈ S, ∑ r ∈ S, (g p - g r) ^ 2 =
          (S.card : ℝ) * g p ^ 2 - 2 * g p * ∑ r ∈ S, g r + ∑ r ∈ S, g r ^ 2 := by
        intro p _
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul]
        rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hmid : ∑ p ∈ S, 2 * g p * ∑ r ∈ S, g r = 2 * (∑ p ∈ S, g p) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sq]; ring
      rw [hmid]; ring
    linarith
  rw [hsq_eq] at hcs
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hR_nn : 0 ≤ x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A := by positivity
  have hsq_le :
      (∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|) ^ 2 ≤
        (Real.sqrt C₀ * (Q : ℝ) * Real.sqrt (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) ^ 2 := by
    have hrhs_eq :
        (Real.sqrt C₀ * (Q : ℝ) * Real.sqrt (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) ^ 2 =
          (Q : ℝ) ^ 2 * (C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC₀.le, Real.sq_sqrt hR_nn]; ring
    rw [hrhs_eq]
    calc (∑ p ∈ S, |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|) ^ 2
        ≤ (S.card : ℝ) * ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x := hcs
      _ ≤ (Q : ℝ) ^ 2 * (C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) :=
          mul_le_mul hcard_le (hbdh x hx Q hQx)
            (Finset.sum_nonneg fun q _ => psiAPVariance_nonneg q x) (sq_nonneg _)
  rw [hsum_eq]
  exact le_of_sq_le_sq hsq_le (by positivity)

/-- **UNCONDITIONAL ALMOST-ALL-MODULI PNT IN ARITHMETIC PROGRESSIONS UP TO `x / (log x)^B` (`0` ASSUMPTIONS!)**:
for EVERY `B ≥ 6`, there exists `C > 0` such that for ALL `x ≥ 4` and ALL `ε > 0`,
letting `Q₀ := ⌊√x⌋₊` and `Q := ⌊x / (log x)^B⌋₊`, the number of reduced pairs `(q, a)` with
`q ∈ (Q₀, Q]` and `|ψ(x; q, a) - x / φ(q)| ≥ ε * (x / φ(q))` satisfies:
`Bad.card ≤ C * Q² / (ε² * (Real.log x)^(B - 3))`. -/
theorem almost_all_ap_pnt_from_bdh {B : ℝ} (hB : 6 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x → ∀ ε : ℝ, 0 < ε →
        let Q₀ : ℕ := ⌊Real.sqrt x⌋₊
        let Q : ℕ := ⌊x / (Real.log x) ^ B⌋₊
        let Bad :=
          ((Finset.Ioc Q₀ Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))).filter
            (fun p => ε * (x / (p.1.totient : ℝ)) ≤
              |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|)
        (Bad.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3))) := by
  have hA : 0 < 2 * B - 3 := by linarith
  obtain ⟨C₀, hC₀, hbdh⟩ := barban_davenport_halberstam_full hA
  refine ⟨2 * C₀, by positivity, fun x hx ε hε => ?_⟩
  dsimp only
  set Q₀ : ℕ := ⌊Real.sqrt x⌋₊
  set Q : ℕ := ⌊x / (Real.log x) ^ B⌋₊
  set Bad :=
    ((Finset.Ioc Q₀ Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))).filter
      (fun p => ε * (x / (p.1.totient : ℝ)) ≤
        |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|)
  have hx0 : 0 < x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
  by_cases hQ0 : Q = 0
  · have hBad_empty : Bad = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
      omega
    rw [hBad_empty, Finset.card_empty, Nat.cast_zero, hQ0]
    simp
  · have hQ1 : 1 ≤ Q := by omega
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
    have hQ_le_div : (Q : ℝ) ≤ x / (Real.log x) ^ B := Nat.floor_le (by positivity)
    have hQx : (Q : ℝ) ≤ x := hQ_le_div.trans (div_le_self hx0.le (Real.one_le_rpow hLx_ge1 (by linarith)))
    set S : Finset (Σ _ : ℕ, ℕ) :=
      (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
    have hBad_sub : Bad ⊆ S := fun p hp => by
      simp only [Bad, S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨by omega, hp.1.1.2⟩, hp.1.2⟩
    have hmarkov : (Bad.card : ℝ) * (ε * x / (Q : ℝ)) ^ 2 ≤ ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x := by
      have hterm : ∀ p ∈ Bad,
          (ε * x / (Q : ℝ)) ^ 2 ≤
            (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)) ^ 2 := by
        intro p hp
        simp only [Bad, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Ioc] at hp
        have hp1_pos : 0 < p.1 := by omega
        have hphi_pos : (0 : ℝ) < (p.1.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hp1_pos)
        have hphi_le_Q : (p.1.totient : ℝ) ≤ (Q : ℝ) := by
          exact_mod_cast (Nat.totient_le p.1).trans hp.1.1.2
        have hlo : ε * x / (Q : ℝ) ≤
            |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| := by
          calc ε * x / (Q : ℝ) = ε * (x / (Q : ℝ)) := by ring
            _ ≤ ε * (x / (p.1.totient : ℝ)) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hx0.le hphi_pos hphi_le_Q) hε.le
            _ ≤ |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| := hp.2
        have hsq := pow_le_pow_left₀ (by positivity) hlo 2
        rwa [sq_abs] at hsq
      calc (Bad.card : ℝ) * (ε * x / (Q : ℝ)) ^ 2
          = ∑ _p ∈ Bad, (ε * x / (Q : ℝ)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ Bad, (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)) ^ 2 :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ p ∈ S, (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hBad_sub fun _ _ _ => sq_nonneg _
        _ = ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q x := Finset.sum_sigma _ _ _
    have hvar := hbdh x hx Q hQx
    have hcomb : (Bad.card : ℝ) * (ε * x / (Q : ℝ)) ^ 2 ≤
        C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ (2 * B - 3)) :=
      hmarkov.trans hvar
    have hden_pos : 0 < (ε * x / (Q : ℝ)) ^ 2 := by positivity
    have hdiv := (le_div_iff₀ hden_pos).mpr hcomb
    have hpowB : (Real.log x) ^ B = (Real.log x) ^ (B - 3) * (Real.log x) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.rpow_natCast (Real.log x) 3,
        ← Real.rpow_add hLx_pos]
      congr 1; push_cast; ring
    have ht1 : x * (Q : ℝ) * (Real.log x) ^ 3 / (ε * x / (Q : ℝ)) ^ 2 ≤
        (Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3)) := by
      have hEq : x * (Q : ℝ) * (Real.log x) ^ 3 / (ε * x / (Q : ℝ)) ^ 2 =
          ((Q : ℝ) / x) * ((Q : ℝ) ^ 2 * (Real.log x) ^ 3 / ε ^ 2) := by
        field_simp [hε.ne', hx0.ne', hQpos.ne']
      rw [hEq]
      have hQdivx : (Q : ℝ) / x ≤ 1 / (Real.log x) ^ B := by
        rw [div_le_iff₀ hx0]
        calc (Q : ℝ) ≤ x / (Real.log x) ^ B := hQ_le_div
          _ = 1 / (Real.log x) ^ B * x := by ring
      calc ((Q : ℝ) / x) * ((Q : ℝ) ^ 2 * (Real.log x) ^ 3 / ε ^ 2)
          ≤ (1 / (Real.log x) ^ B) * ((Q : ℝ) ^ 2 * (Real.log x) ^ 3 / ε ^ 2) :=
            mul_le_mul_of_nonneg_right hQdivx (by positivity)
        _ = (Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3)) := by
            rw [hpowB]
            field_simp [hε.ne', hLx_pos.ne', (Real.rpow_pos_of_pos hLx_pos (B - 3)).ne']
    have ht2 : (x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2 ≤
        (Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3)) := by
      have hEq : (x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2 =
          (Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (2 * B - 3)) := by
        field_simp [hε.ne', hx0.ne', hQpos.ne', (Real.rpow_pos_of_pos hLx_pos (2 * B - 3)).ne']
      rw [hEq]
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLx_ge1 (by linarith)) (sq_nonneg ε)
    have hsplit_div :
        C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2 =
          C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 / (ε * x / (Q : ℝ)) ^ 2 +
            (x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2) := by ring
    calc (Bad.card : ℝ)
        ≤ C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2 := hdiv
      _ = C₀ * (x * (Q : ℝ) * (Real.log x) ^ 3 / (ε * x / (Q : ℝ)) ^ 2 +
            (x ^ 2 / (Real.log x) ^ (2 * B - 3)) / (ε * x / (Q : ℝ)) ^ 2) := hsplit_div
      _ ≤ C₀ * ((Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3)) +
            (Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3))) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₀.le
      _ = (2 * C₀) * ((Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3))) := by ring

/-- **Zero-Density Limit Corollary of `almost_all_ap_pnt_from_bdh`**:
for EVERY `B ≥ 6` (in particular `B = 10`) and EVERY `ε > 0`, the fraction of reduced pairs `(q, a)`
with `q ∈ (√x, x / (log x)^B]` violating `|ψ(x; q, a) - x / φ(q)| < ε * (x / φ(q))` tends to `0` as `x → ∞`! -/
theorem almost_all_ap_pnt_density_tendsto_zero {B : ℝ} (hB : 6 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      ((((Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊x / (Real.log x) ^ B⌋₊).sigma
          (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))).filter
          (fun p => ε * (x / (p.1.totient : ℝ)) ≤
            |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|)).card : ℝ) /
        ((⌊x / (Real.log x) ^ B⌋₊ : ℝ) ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := almost_all_ap_pnt_from_bdh hB
  refine squeeze_zero' (g := fun x : ℝ => C / (ε ^ 2 * (Real.log x) ^ (B - 3))) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x _
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    set Q : ℕ := ⌊x / (Real.log x) ^ B⌋₊
    by_cases hQ0 : Q = 0
    · simp only [Q] at hQ0 ⊢
      rw [hQ0, Nat.cast_zero, zero_pow two_ne_zero, div_zero]
      have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
      positivity
    · have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
      have h1 := hbd x hx ε hε
      rw [div_le_iff₀ (sq_pos_of_pos hQpos)]
      calc _ ≤ C * ((Q : ℝ) ^ 2 / (ε ^ 2 * (Real.log x) ^ (B - 3))) := h1
        _ = C / (ε ^ 2 * (Real.log x) ^ (B - 3)) * (Q : ℝ) ^ 2 := by ring
  · have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ (B - 3)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : 0 < B - 3)).comp Real.tendsto_log_atTop
    have hden : Tendsto (fun x : ℝ => ε ^ 2 * (Real.log x) ^ (B - 3)) atTop atTop :=
      Tendsto.const_mul_atTop (sq_pos_of_pos hε) hpow
    have hinv : Tendsto (fun x : ℝ => C * (ε ^ 2 * (Real.log x) ^ (B - 3))⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hden).const_mul C
    exact hinv.congr fun x => by rw [div_eq_mul_inv]

open Classical in
/-- **UNCONDITIONAL ALMOST-ALL-MODULI PRIMES IN `(x, 2x]` VIA BDH + `exists_prime_in_Ioc_of_psiAP_diff_gt`**:
for EVERY `A > 0`, there exists `C > 0` such that for ALL `x ≥ 4`, letting
`Q := ⌊√x / (8 * log(2 * x))⌋₊`, the number of reduced pairs `(q, a)` with `1 ≤ q ≤ Q`, `a < q`,
`Nat.Coprime a q` that contain NO prime `p ≡ a [MOD q]` in `(x, 2 * x]` is at most
`C * Q² / (Real.log x)^A`! -/
theorem almost_all_ap_primes_from_bdh {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 4 ≤ x →
        let Q : ℕ := ⌊Real.sqrt x / (8 * Real.log (2 * x))⌋₊
        let NoPrime :=
          ((Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))).filter
            (fun p => ¬ ∃ r : ℕ, r.Prime ∧ r ≡ p.2 [MOD p.1] ∧ x < (r : ℝ) ∧ (r : ℝ) ≤ 2 * x)
        (NoPrime.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by
  obtain ⟨C₀, hC₀, hbdh⟩ := barban_davenport_halberstam_full hA
  -- Absorb `(Real.log (2 * x)) ^ (A + 3) ≤ C_log * √x` for `x ≥ 4` via `pow_mul_exp_neg_le_one`
  set k : ℕ := ⌈A + 3⌉₊ + 1
  have hk_pos : 0 < k := Nat.succ_pos _
  have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  set C_log : ℝ := (2 * (k : ℝ)) ^ k
  have hC_log_pos : 0 < C_log := by positivity
  have hlog_le_sqrt : ∀ x : ℝ, 4 ≤ x → (Real.log x) ^ (A + 3) ≤ C_log * Real.sqrt x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
      have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
    have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
    have hA3_le_k : A + 3 ≤ (k : ℝ) := by
      have h1 : A + 3 ≤ (⌈A + 3⌉₊ : ℝ) := Nat.le_ceil _
      dsimp only [k]; push_cast; linarith
    have h1 : (Real.log x) ^ (A + 3) ≤ (Real.log x) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hLx_ge1 hA3_le_k
    have h2 : (Real.log x) ^ k * Real.exp (-(1 / 2 : ℝ) * Real.log x) ≤ C_log := by
      have hEq : (Real.log x) ^ k * Real.exp (-(1 / 2 : ℝ) * Real.log x) =
          C_log * ((Real.log x / (2 * (k : ℝ))) ^ k *
            Real.exp (-(k : ℝ) * (Real.log x / (2 * (k : ℝ))))) := by
        have ha : -(k : ℝ) * (Real.log x / (2 * (k : ℝ))) = -(1 / 2 : ℝ) * Real.log x := by
          field_simp [hkR_pos.ne']
        have hb : C_log * (Real.log x / (2 * (k : ℝ))) ^ k = (Real.log x) ^ k := by
          dsimp only [C_log]; rw [← mul_pow]; congr 1; field_simp [hkR_pos.ne']
        rw [ha, ← mul_assoc, hb]
      rw [hEq]
      exact (mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one k (by positivity)) hC_log_pos.le).trans_eq (mul_one _)
    have hexp_sqrt : Real.exp (-(1 / 2 : ℝ) * Real.log x) = (Real.sqrt x)⁻¹ := by
      rw [show -(1 / 2 : ℝ) * Real.log x = -((1 / 2 : ℝ) * Real.log x) by ring, Real.exp_neg,
        Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, mul_comm]
    rw [hexp_sqrt, ← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr hx0)] at h2
    linarith
  set C_fin : ℝ := 72 * C₀ * (2 ^ (A + 3) * C_log + 1)
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨C_fin, hC_fin_pos, fun x hx4 => ?_⟩
  dsimp only
  set Q : ℕ := ⌊Real.sqrt x / (8 * Real.log (2 * x))⌋₊
  set S := (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
  set NoPrime := S.filter
    (fun p => ¬ ∃ r : ℕ, r.Prime ∧ r ≡ p.2 [MOD p.1] ∧ x < (r : ℝ) ∧ (r : ℝ) ≤ 2 * x)
  have hx0 : 0 < x := by linarith
  have hLx_ge1 : (1 : ℝ) ≤ Real.log x := by
    have he4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    exact ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))).le
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans_le hLx_ge1
  have hL2x_pos : 0 < Real.log (2 * x) := Real.log_pos (by linarith)
  by_cases hQ0 : Q = 0
  · have hEmpty : NoPrime = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      simp only [S, Finset.mem_sigma, Finset.mem_Icc] at hp
      omega
    rw [hEmpty, Finset.card_empty, Nat.cast_zero, hQ0]
    simp
  · have hQ1 : 1 ≤ Q := by omega
    have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ1
    have hQ_le : (Q : ℝ) ≤ Real.sqrt x / (8 * Real.log (2 * x)) := Nat.floor_le (by positivity)
    have hQ_le_sqrt : (Q : ℝ) ≤ Real.sqrt x := by
      have h8 : (1 : ℝ) ≤ 8 * Real.log (2 * x) := by
        have h1 : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
        linarith
      exact hQ_le.trans (div_le_self (Real.sqrt_nonneg x) h8)
    have hsqrt_le_x : Real.sqrt x ≤ x := by
      have hsq : Real.sqrt x ^ 2 ≤ x ^ 2 := by rw [Real.sq_sqrt hx0.le]; nlinarith
      exact le_of_sq_le_sq hsq hx0.le
    have hQx : (Q : ℝ) ≤ x := hQ_le_sqrt.trans hsqrt_le_x
    have hQ2x : (Q : ℝ) ≤ 2 * x := by linarith
    -- Define the bad sets at `x` and `2 * x` with relative threshold `1 / 6`
    set Bad₁ := S.filter (fun p => (1 / 6 : ℝ) * (x / (p.1.totient : ℝ)) ≤
      |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)|)
    set Bad₂ := S.filter (fun p => (1 / 6 : ℝ) * ((2 * x) / (p.1.totient : ℝ)) ≤
      |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 (2 * x) - (2 * x) / (p.1.totient : ℝ)|)
    -- Every pair NOT in `Bad₁ ∪ Bad₂` DOES contain a prime `r ≡ a [MOD q]` in `(x, 2 * x]`!
    have hsub : NoPrime ⊆ Bad₁ ∪ Bad₂ := by
      intro p hp
      simp only [NoPrime, Finset.mem_filter] at hp
      obtain ⟨hpS, hno⟩ := hp
      by_contra hnot
      rw [Finset.mem_union] at hnot
      push Not at hnot
      obtain ⟨hn1, hn2⟩ := hnot
      simp only [Bad₁, Bad₂, Finset.mem_filter] at hn1 hn2
      have hlt1 : |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x - x / (p.1.totient : ℝ)| <
          (1 / 6 : ℝ) * (x / (p.1.totient : ℝ)) := lt_of_not_ge (fun h => hn1 ⟨hpS, h⟩)
      have hlt2 : |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 (2 * x) - (2 * x) / (p.1.totient : ℝ)| <
          (1 / 6 : ℝ) * ((2 * x) / (p.1.totient : ℝ)) := lt_of_not_ge (fun h => hn2 ⟨hpS, h⟩)
      have h1_hi := (abs_lt.mp hlt1).2
      have h2_lo := (abs_lt.mp hlt2).1
      have hdiff_gt : (1 / 2 : ℝ) * (x / (p.1.totient : ℝ)) <
          Stage2DirichletAP.chebyshevPsiAP p.1 p.2 (2 * x) -
            Stage2DirichletAP.chebyshevPsiAP p.1 p.2 x := by
        have hlin : (2 * x) / (p.1.totient : ℝ) - (1 / 6 : ℝ) * ((2 * x) / (p.1.totient : ℝ)) -
            (x / (p.1.totient : ℝ) + (1 / 6 : ℝ) * (x / (p.1.totient : ℝ))) =
            (1 / 2 : ℝ) * (x / (p.1.totient : ℝ)) := by ring
        linarith
      simp only [S, Finset.mem_sigma, Finset.mem_Icc] at hpS
      have hphi_pos : (0 : ℝ) < (p.1.totient : ℝ) :=
        Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
      have hphi_le_Q : (p.1.totient : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast (Nat.totient_le p.1).trans hpS.1.2
      have hphi_le : (p.1.totient : ℝ) ≤ Real.sqrt x / (8 * Real.log (2 * x)) := hphi_le_Q.trans hQ_le
      have hsqrt_lt : Real.sqrt (2 * x) * Real.log (2 * x) < (1 / 2 : ℝ) * (x / (p.1.totient : ℝ)) := by
        have h1 : 4 * Real.sqrt x * Real.log (2 * x) ≤ (1 / 2 : ℝ) * (x / (p.1.totient : ℝ)) := by
          have hdiv := div_le_div_of_nonneg_left hx0.le hphi_pos hphi_le
          have hEq : (1 / 2 : ℝ) * (x / (Real.sqrt x / (8 * Real.log (2 * x)))) =
              4 * Real.sqrt x * Real.log (2 * x) := by
            have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
            have hs_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
            have hmul : (1 / 2 : ℝ) * (x / (Real.sqrt x / (8 * Real.log (2 * x)))) * Real.sqrt x =
                (4 * Real.sqrt x * Real.log (2 * x)) * Real.sqrt x := by
              rw [div_div_eq_mul_div, mul_div_assoc', div_mul_cancel₀ _ hs_ne]
              linear_combination (4 * Real.log (2 * x)) * hsq.symm
            exact mul_right_cancel₀ hs_ne hmul
          nlinarith
        have h2 : Real.sqrt (2 * x) < 4 * Real.sqrt x := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          have hrt2 : Real.sqrt 2 < 4 := by
            have hsq : Real.sqrt 2 ^ 2 < 4 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
            nlinarith [Real.sqrt_nonneg 2]
          nlinarith [Real.sqrt_pos.mpr hx0]
        nlinarith
      exact hno (Stage2DirichletAP.exists_prime_in_Ioc_of_psiAP_diff_gt p.1 p.2
        (by linarith) (by linarith) (hsqrt_lt.trans hdiff_gt))
    -- Helper Markov bound for `Bad(y)` at `y ∈ {x, 2 * x}`!
    have hmarkov_at : ∀ y : ℝ, x ≤ y → y ≤ 2 * x →
        ((S.filter (fun p => (1 / 6 : ℝ) * (y / (p.1.totient : ℝ)) ≤
          |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)|)).card : ℝ) ≤
          36 * C₀ * (2 ^ (A + 3) * C_log + 1) * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by
      intro y hxy hy2x
      have hy4 : 4 ≤ y := hx4.trans hxy
      have hy0 : 0 < y := by linarith
      have hQy : (Q : ℝ) ≤ y := hQx.trans hxy
      set By := S.filter (fun p => (1 / 6 : ℝ) * (y / (p.1.totient : ℝ)) ≤
        |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)|)
      have hmk : (By.card : ℝ) * ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 ≤
          ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q y := by
        have hterm : ∀ p ∈ By,
            ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 ≤
              (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)) ^ 2 := by
          intro p hp
          simp only [By, S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc] at hp
          have hphi_pos : (0 : ℝ) < (p.1.totient : ℝ) :=
            Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
          have hphi_le_Q : (p.1.totient : ℝ) ≤ (Q : ℝ) := by
            exact_mod_cast (Nat.totient_le p.1).trans hp.1.1.2
          have hlo : (1 / 6 : ℝ) * y / (Q : ℝ) ≤
              |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)| := by
            calc (1 / 6 : ℝ) * y / (Q : ℝ) = (1 / 6 : ℝ) * (y / (Q : ℝ)) := by ring
              _ ≤ (1 / 6 : ℝ) * (y / (p.1.totient : ℝ)) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hy0.le hphi_pos hphi_le_Q) (by norm_num)
              _ ≤ |Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)| := hp.2
          have hsq := pow_le_pow_left₀ (by positivity) hlo 2
          rwa [sq_abs] at hsq
        calc (By.card : ℝ) * ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2
            = ∑ _p ∈ By, ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ By, (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)) ^ 2 :=
              Finset.sum_le_sum hterm
          _ ≤ ∑ p ∈ S, (Stage2DirichletAP.chebyshevPsiAP p.1 p.2 y - y / (p.1.totient : ℝ)) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
          _ = ∑ q ∈ Finset.Icc 1 Q, psiAPVariance q y := Finset.sum_sigma _ _ _
      have hvar := hbdh y hy4 Q hQy
      have hden_pos : 0 < ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 := by positivity
      have hdiv := (le_div_iff₀ hden_pos).mpr (hmk.trans hvar)
      have hLy_ge : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
      have hLy_le : Real.log y ≤ 2 * Real.log x := by
        have h1 : y ≤ x ^ 2 := by nlinarith
        calc Real.log y ≤ Real.log (x ^ 2) := Real.log_le_log hy0 h1
          _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
      have hLy_pos : 0 < Real.log y := hLx_pos.trans_le hLy_ge
      have ht1 : y * (Q : ℝ) * (Real.log y) ^ 3 / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 ≤
          36 * (2 ^ (A + 3) * C_log) * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by
        have hEq : y * (Q : ℝ) * (Real.log y) ^ 3 / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 =
            36 * ((Q : ℝ) / y) * (Real.log y) ^ 3 * (Q : ℝ) ^ 2 := by
          field_simp [hy0.ne', hQpos.ne']; ring
        rw [hEq]
        have hQdivy : (Q : ℝ) / y ≤ 1 / Real.sqrt x := by
          rw [div_le_div_iff₀ hy0 (Real.sqrt_pos.mpr hx0), one_mul]
          calc (Q : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
                mul_le_mul_of_nonneg_right hQ_le_sqrt (Real.sqrt_nonneg x)
            _ = x := Real.mul_self_sqrt hx0.le
            _ ≤ y := hxy
        have hLy3 : (Real.log y) ^ 3 ≤ 2 ^ (A + 3) * (Real.log x) ^ 3 := by
          have h1 : (Real.log y) ^ 3 ≤ (2 * Real.log x) ^ 3 := pow_le_pow_left₀ hLy_pos.le hLy_le 3
          have h2 : (2 : ℝ) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (A + 3) := by
            rw [← Real.rpow_natCast (2 : ℝ) 3]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
          rw [mul_pow] at h1
          nlinarith [pow_nonneg hLx_pos.le 3]
        have hlog_div : (Real.log x) ^ 3 / Real.sqrt x ≤ C_log / (Real.log x) ^ A := by
          rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) (Real.rpow_pos_of_pos hLx_pos A)]
          have hpow : (Real.log x) ^ 3 * (Real.log x) ^ A = (Real.log x) ^ (A + 3) := by
            rw [← Real.rpow_natCast (Real.log x) 3, ← Real.rpow_add hLx_pos]; congr 1; push_cast; ring
          rw [hpow]; exact hlog_le_sqrt x hx4
        calc 36 * ((Q : ℝ) / y) * (Real.log y) ^ 3 * (Q : ℝ) ^ 2
            ≤ 36 * (1 / Real.sqrt x) * (2 ^ (A + 3) * (Real.log x) ^ 3) * (Q : ℝ) ^ 2 := by gcongr
          _ = 36 * 2 ^ (A + 3) * ((Real.log x) ^ 3 / Real.sqrt x) * (Q : ℝ) ^ 2 := by ring
          _ ≤ 36 * 2 ^ (A + 3) * (C_log / (Real.log x) ^ A) * (Q : ℝ) ^ 2 := by gcongr
          _ = 36 * (2 ^ (A + 3) * C_log) * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by ring
      have ht2 : (y ^ 2 / (Real.log y) ^ A) / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 ≤
          36 * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by
        have hEq : (y ^ 2 / (Real.log y) ^ A) / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 =
            36 * ((Q : ℝ) ^ 2 / (Real.log y) ^ A) := by
          field_simp [hy0.ne', hQpos.ne', (Real.rpow_pos_of_pos hLy_pos A).ne']; ring
        rw [hEq]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hLx_pos A)
          (Real.rpow_le_rpow hLx_pos.le hLy_ge hA.le)
      have hsplit_div :
          C₀ * (y * (Q : ℝ) * (Real.log y) ^ 3 + y ^ 2 / (Real.log y) ^ A) / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 =
            C₀ * (y * (Q : ℝ) * (Real.log y) ^ 3 / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 +
              (y ^ 2 / (Real.log y) ^ A) / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2) := by ring
      calc (By.card : ℝ)
          ≤ C₀ * (y * (Q : ℝ) * (Real.log y) ^ 3 + y ^ 2 / (Real.log y) ^ A) /
              ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 := hdiv
        _ = C₀ * (y * (Q : ℝ) * (Real.log y) ^ 3 / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2 +
              (y ^ 2 / (Real.log y) ^ A) / ((1 / 6 : ℝ) * y / (Q : ℝ)) ^ 2) := hsplit_div
        _ ≤ C₀ * (36 * (2 ^ (A + 3) * C_log) * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) +
              36 * ((Q : ℝ) ^ 2 / (Real.log x) ^ A)) :=
            mul_le_mul_of_nonneg_left (by linarith) hC₀.le
        _ = 36 * C₀ * (2 ^ (A + 3) * C_log + 1) * ((Q : ℝ) ^ 2 / (Real.log x) ^ A) := by ring
    have hcard_union : (NoPrime.card : ℝ) ≤ (Bad₁.card : ℝ) + (Bad₂.card : ℝ) := by
      have hnat : NoPrime.card ≤ Bad₁.card + Bad₂.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le Bad₁ Bad₂)
      exact_mod_cast hnat
    have hb1 := hmarkov_at x le_rfl (by linarith)
    have hb2 := hmarkov_at (2 * x) (by linarith) le_rfl
    dsimp only [C_fin]
    linarith

end RHDirect.Stage8BarbanDavenport

end
