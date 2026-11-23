import RHDirect.Interfaces
import RHDirect.ThetaSlopeEngine
import RHDirect.HostFieldSupply
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.NormNum.Prime

/-!
# RHDirect.Stage2PrimePairs

Clean, dead-field-free, zero-`sorry`, zero-custom-`axiom` Lean 4 discharge of the auxiliary
prime-pair supply (`ThetaSlopeEngine.PairEx`, `HostFieldSupply.PairSupply`, and
`HostFieldSupply.SmallOne`) in `rh-direct`.

## Structure
1. **Unconditional Odd-Primorial & Explicit CRT Congruence System**
   (`oddPrimorial`, `pairModulus`, `pairResidue`):
   - Explicit closed-form CRT witness `pairResidue q n := 8 * (q * oddPrimorial n) - 1`
     modulo `pairModulus q n := 16 * (q * oddPrimorial n)` — zero black-box CRT inversion!
   - Exact equivalence `pairModEq_iff`: for any prime `q ≡ 3 (mod 8)` with `n < q`,
     `d ≡ pairResidue q n [MOD pairModulus q n]` holds **if and only if**
     `d % 16 = 7 ∧ q ∣ d + 1 ∧ ∀ p prime ≠ 2, p ≤ n → p ∣ d + 1`.
   - Unconditional coprimality `Nat.Coprime (pairResidue q n) (pairModulus q n)` and
     Erdős/Chebyshev primorial bound `oddPrimorial n ≤ 4 ^ n`.
2. **Unconditional Quadratic Reciprocity, Parity, Coprimality & Infinitude**:
   - Full deduction of `HostFieldSupply.HostHyp q d`, distinctness `q ≠ d`, coprimality,
     supplementary laws `(2|q) = -1`, `(2|d) = 1`, `(-1|q) = (-1|d) = -1`,
     reciprocity `(-d|q) = 1`, `(d|q) = -1`, `(q|d) = 1`, and small-prime splitting
     `(-d|p) = 1` for all odd primes `p ≤ n`.
   - Concrete verified witness `hostHyp_3_23 : HostFieldSupply.HostHyp 3 23`.
   - Unconditional Euclid-style infinitude proofs for primes `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 8)`.
3. **Unconditional Quantitative Modulus & Size Envelope**:
   - `self_le_exp_half`: `U ≤ exp (U / 2)` for all `U ≥ 0`, giving `⌊U⌋₊ < q` automatically.
   - `pairModulus_le_exp_four_mul`: `pairModulus q ⌊U⌋₊ ≤ exp (4 * U)` for `U ≥ 3`, `log q ≤ U`.
   - `winPair_of_congr_and_bounds`: unconditional assembly of `RHDirect.WinPair eps Y q d`.
4. **Exact 1-Line Linnik Prime-in-AP Reduction (`LinnikAPInterval` / `LinnikAPDyadic`)**:
   - Single 1-line standard prime-in-AP predicate `LinnikAPInterval` (classical unconditional
     theorem of Linnik 1944 / Fogels 1965 / Gallagher 1970; also implied by `LinnikAPDyadic`).
   - Proves `LinnikAPInterval → HostFieldSupply.PairSupply`, `LinnikAPInterval → ThetaSlopeEngine.PairEx`,
     and `LinnikAPInterval → HostFieldSupply.SmallOne`, discharging all congruence, CRT,
     reciprocity, parity, distinctness, coprimality, and exponential-scale plumbing unconditionally.
   - Provides direct drop-in wrappers `winPairs_of_vwinAt_of_linnikAPInterval`,
     `hostFieldSupply_assembly_of_linnikAPInterval`, and `minimalThetaEngineInputs_of_linnikAPInterval`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Real Finset RHDirect

namespace RHDirect.Stage2PrimePairs

/-! ## Section 1: Unconditional Odd-Primorial & Explicit CRT Congruence System -/

/-- Finset of all odd primes `p ≤ n`. -/
def oddPrimesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => p.Prime ∧ p ≠ 2

/-- Product of all odd primes `p ≤ n` (the odd primorial up to `n`). -/
def oddPrimorial (n : ℕ) : ℕ :=
  ∏ p ∈ oddPrimesUpTo n, p

/-- Explicit CRT modulus `16 * (q * oddPrimorial n)` for the auxiliary prime `d`. -/
def pairModulus (q n : ℕ) : ℕ :=
  16 * (q * oddPrimorial n)

/-- Explicit closed-form CRT residue `8 * (q * oddPrimorial n) - 1` modulo `pairModulus q n`,
simultaneously encoding `d ≡ 7 (mod 16)`, `q ∣ d + 1`, and `p ∣ d + 1` for all odd primes `p ≤ n`. -/
def pairResidue (q n : ℕ) : ℕ :=
  8 * (q * oddPrimorial n) - 1

theorem mem_oddPrimesUpTo {n p : ℕ} :
    p ∈ oddPrimesUpTo n ↔ p ≤ n ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimesUpTo]

theorem odd_of_mem_oddPrimesUpTo {n p : ℕ} (hp : p ∈ oddPrimesUpTo n) : Odd p := by
  obtain ⟨_, hpr, hne2⟩ := mem_oddPrimesUpTo.mp hp
  exact hpr.odd_of_ne_two hne2

private theorem odd_prod_of_odd {s : Finset ℕ} (hs : ∀ p ∈ s, Odd p) :
    Odd (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hs a (Finset.mem_insert_self a s)).mul
      (ih fun p hp => hs p (Finset.mem_insert_of_mem hp))

theorem odd_oddPrimorial (n : ℕ) : Odd (oddPrimorial n) :=
  odd_prod_of_odd fun _ hp => odd_of_mem_oddPrimesUpTo hp

theorem oddPrimorial_pos (n : ℕ) : 0 < oddPrimorial n := by
  obtain ⟨k, hk⟩ := odd_oddPrimorial n
  omega

theorem dvd_oddPrimorial {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ n) :
    p ∣ oddPrimorial n :=
  Finset.dvd_prod_of_mem _ (mem_oddPrimesUpTo.mpr ⟨hpn, hp, hp2⟩)

private theorem prod_primes_dvd_iff {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {m : ℕ} :
    (∏ p ∈ s, p) ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_prime : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    constructor
    · intro h p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact (dvd_mul_right p _).trans h
      · exact (ih hs').mp ((dvd_mul_left _ a).trans h) p hp
    · intro h
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes ha_prime (hs' p hp)).mpr fun heq => ha (heq ▸ hp)
      exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a s))
        ((ih hs').mpr fun p hp => h p (Finset.mem_insert_of_mem hp))

theorem oddPrimorial_dvd_iff (n m : ℕ) :
    oddPrimorial n ∣ m ↔ ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ m := by
  unfold oddPrimorial
  rw [prod_primes_dvd_iff fun p hp => (mem_oddPrimesUpTo.mp hp).2.1]
  constructor
  · intro h p hp hp2 hpn
    exact h p (mem_oddPrimesUpTo.mpr ⟨hpn, hp, hp2⟩)
  · intro h p hp
    obtain ⟨hpn, hpr, hp2⟩ := mem_oddPrimesUpTo.mp hp
    exact h p hpr hp2 hpn

theorem coprime_of_gt_oddPrimorial {n q : ℕ} (hq : q.Prime) (hnq : n < q) :
    Nat.Coprime q (oddPrimorial n) := by
  unfold oddPrimorial
  refine Nat.Coprime.prod_right fun p hp => ?_
  obtain ⟨hpn, hpr, _⟩ := mem_oddPrimesUpTo.mp hp
  exact (Nat.coprime_primes hq hpr).mpr (by omega)

theorem oddPrimorial_dvd_primorial (n : ℕ) : oddPrimorial n ∣ primorial n := by
  unfold oddPrimorial primorial
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
  obtain ⟨hpn, hpr, _⟩ := mem_oddPrimesUpTo.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr⟩

/-- Unconditional Erdős/Chebyshev exponential bound `oddPrimorial n ≤ 4 ^ n`. -/
theorem oddPrimorial_le_four_pow (n : ℕ) : oddPrimorial n ≤ 4 ^ n :=
  (Nat.le_of_dvd (primorial_pos n) (oddPrimorial_dvd_primorial n)).trans (primorial_le_four_pow n)

/-- Closed-form congruence mod 16: for any odd `R`, `8 * R - 1 ≡ 7 (mod 16)`. -/
theorem eight_mul_sub_one_mod_sixteen {R : ℕ} (hR : Odd R) : (8 * R - 1) % 16 = 7 := by
  obtain ⟨k, rfl⟩ := hR
  omega

/-- Closed-form coprimality: for any odd `R`, `gcd(8 * R - 1, 16 * R) = 1`. -/
theorem coprime_eight_mul_sub_one_sixteen_mul {R : ℕ} (hR : Odd R) :
    Nat.Coprime (8 * R - 1) (16 * R) := by
  have hRpos : 1 ≤ R := by obtain ⟨k, rfl⟩ := hR; omega
  have h16 : Nat.Coprime (8 * R - 1) 16 := by
    have h2 : Nat.Coprime (8 * R - 1) 2 :=
      Nat.coprime_two_right.mpr ⟨4 * R - 1, by omega⟩
    simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using h2.pow_right 4
  have hRcop : Nat.Coprime (8 * R - 1) R := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : Nat.gcd (8 * R - 1) R ∣ 8 * R - 1 := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd (8 * R - 1) R ∣ 8 * R :=
      (Nat.gcd_dvd_right _ _).trans (dvd_mul_left R 8)
    have hd3 : Nat.gcd (8 * R - 1) R ∣ 1 := by
      have hsub := Nat.dvd_sub hd2 hd1
      rwa [show 8 * R - (8 * R - 1) = 1 by omega] at hsub
    exact Nat.dvd_one.mp hd3
  exact h16.mul_right hRcop

theorem odd_mul_oddPrimorial {q n : ℕ} (hq : q % 8 = 3) : Odd (q * oddPrimorial n) :=
  (Nat.odd_iff.mpr (by omega)).mul (odd_oddPrimorial n)

theorem coprime_pairResidue_pairModulus {q n : ℕ} (hq : q % 8 = 3) :
    Nat.Coprime (pairResidue q n) (pairModulus q n) :=
  coprime_eight_mul_sub_one_sixteen_mul (odd_mul_oddPrimorial hq)

theorem two_le_pairModulus {q n : ℕ} (hq : q % 8 = 3) : 2 ≤ pairModulus q n := by
  have hR : 1 ≤ q * oddPrimorial n := by
    obtain ⟨k, hk⟩ := odd_mul_oddPrimorial (n := n) hq
    omega
  unfold pairModulus
  omega

/-- Forward direction of the CRT congruence system (requires no `n < q` hypothesis):
any `d ≡ pairResidue q n [MOD pairModulus q n]` satisfies `d % 16 = 7`, `q ∣ d + 1`,
and `p ∣ d + 1` for every odd prime `p ≤ n`. -/
theorem pairModEq_imp {q n d : ℕ} (hq : q % 8 = 3)
    (hd : d ≡ pairResidue q n [MOD pairModulus q n]) :
    d % 16 = 7 ∧ q ∣ d + 1 ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ d + 1) := by
  set R := q * oddPrimorial n
  have hR : Odd R := odd_mul_oddPrimorial hq
  have hRpos : 1 ≤ R := by obtain ⟨k, hk⟩ := hR; omega
  have hmod16 : d % 16 = 7 := by
    have h1 : d ≡ 8 * R - 1 [MOD 16] := hd.of_dvd (dvd_mul_right 16 R)
    exact Eq.trans h1 (eight_mul_sub_one_mod_sixteen hR)
  have hRdvd : R ∣ d + 1 := by
    have h1 : d ≡ 8 * R - 1 [MOD R] := hd.of_dvd (dvd_mul_left R 16)
    have h2 : d + 1 ≡ 8 * R - 1 + 1 [MOD R] := h1.add_right 1
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 8 * R)] at h2
    exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left R 8)))
  refine ⟨hmod16, (dvd_mul_right q _).trans hRdvd, fun p hp hp2 hpn => ?_⟩
  exact ((dvd_oddPrimorial hp hp2 hpn).trans (dvd_mul_left _ q)).trans hRdvd

/-- **Exact CRT Equivalence (`pairModEq_iff`)**:
For any prime `q ≡ 3 (mod 8)` with `n < q`, the single linear congruence
`d ≡ pairResidue q n [MOD pairModulus q n]` is **equivalent** to the entire system
`d % 16 = 7 ∧ q ∣ d + 1 ∧ ∀ p prime ≠ 2, p ≤ n → p ∣ d + 1`. -/
theorem pairModEq_iff {q n d : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3) (hnq : n < q) :
    d ≡ pairResidue q n [MOD pairModulus q n] ↔
      d % 16 = 7 ∧ q ∣ d + 1 ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ d + 1) := by
  refine ⟨pairModEq_imp hq8, ?_⟩
  rintro ⟨hd16, hqd, hsmall⟩
  set R := q * oddPrimorial n
  have hR : Odd R := odd_mul_oddPrimorial hq8
  have hRpos : 1 ≤ R := by obtain ⟨k, hk⟩ := hR; omega
  have hPdvd : oddPrimorial n ∣ d + 1 := (oddPrimorial_dvd_iff n (d + 1)).mpr hsmall
  have hRdvd : R ∣ d + 1 := (coprime_of_gt_oddPrimorial hq hnq).mul_dvd_of_dvd_of_dvd hqd hPdvd
  have hmod16 : d ≡ 8 * R - 1 [MOD 16] := by
    change d % 16 = (8 * R - 1) % 16
    rw [hd16, eight_mul_sub_one_mod_sixteen hR]
  have hmodR : d ≡ 8 * R - 1 [MOD R] := by
    have hadd : d + 1 ≡ (8 * R - 1) + 1 [MOD R] := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 8 * R)]
      exact (Nat.modEq_zero_iff_dvd.mpr hRdvd).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left R 8)).symm
    exact Nat.ModEq.add_right_cancel' 1 hadd
  have hcop16R : Nat.Coprime 16 R := by
    have h2R : Nat.Coprime 2 R := Nat.coprime_two_left.mpr hR
    simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using h2R.pow_left 4
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop16R).mp ⟨hmod16, hmodR⟩

/-! ## Section 2: Unconditional Reciprocity, Parity, Coprimality & Infinitude -/

/-- Unconditional construction of `HostFieldSupply.HostHyp q d` from the CRT congruence. -/
theorem hostHyp_of_pairModEq {q n d : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3) (hd : d.Prime)
    (hcongr : d ≡ pairResidue q n [MOD pairModulus q n]) :
    HostFieldSupply.HostHyp q d := by
  obtain ⟨hd16, hqd, _⟩ := pairModEq_imp hq8 hcongr
  exact ⟨hq, hd, hq8, hd16, HostFieldSupply.jacobiSym_neg_of_dvd_succ hqd⟩

/-- **Complete Unconditional Reciprocity, Supplementary-Law & Splitting Package**:
Discharges all quadratic reciprocity, supplementary-law, parity, distinctness, coprimality,
and small-prime splitting identities from `d ≡ pairResidue q n [MOD pairModulus q n]`. -/
theorem reciprocity_of_pairModEq {q n d : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3) (hd : d.Prime)
    (hcongr : d ≡ pairResidue q n [MOD pairModulus q n]) :
    HostFieldSupply.HostHyp q d ∧
      q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ Nat.Coprime q d ∧
      jacobiSym (-1 : ℤ) q = -1 ∧ jacobiSym (-1 : ℤ) d = -1 ∧
      jacobiSym (2 : ℤ) q = -1 ∧ jacobiSym (2 : ℤ) d = 1 ∧
      jacobiSym (-(d : ℤ)) q = 1 ∧ jacobiSym (d : ℤ) q = -1 ∧ jacobiSym (q : ℤ) d = 1 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → jacobiSym (-(d : ℤ)) p = 1) := by
  obtain ⟨hd16, hqd, hsmall⟩ := pairModEq_imp hq8 hcongr
  have hH : HostFieldSupply.HostHyp q d :=
    ⟨hq, hd, hq8, hd16, HostFieldSupply.jacobiSym_neg_of_dvd_succ hqd⟩
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hd8 : d % 8 = 7 := by omega
  have hneg_q : jacobiSym (-1 : ℤ) q = -1 :=
    HostFieldSupply.jacobiSym_neg_one_of_mod_four_eq_three hq4
  have hneg_d : jacobiSym (-1 : ℤ) d = -1 :=
    HostFieldSupply.jacobiSym_neg_one_of_mod_four_eq_three hd4
  have h2_q : jacobiSym (2 : ℤ) q = -1 := by
    rw [jacobiSym.at_two hH.odd_q]
    have : ZMod.χ₈ (q : ZMod 8) = ZMod.χ₈ (3 : ZMod 8) := by
      congr 1
      rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]
      change q % 8 = 3 % 8
      omega
    simpa [ZMod.χ₈] using this
  have h2_d : jacobiSym (2 : ℤ) d = 1 := by
    rw [jacobiSym.at_two hH.odd_d]
    have : ZMod.χ₈ (d : ZMod 8) = ZMod.χ₈ (7 : ZMod 8) := by
      congr 1
      rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]
      change d % 8 = 7 % 8
      omega
    simpa [ZMod.χ₈] using this
  have hneg_dq : jacobiSym (-(d : ℤ)) q = 1 := hH.jac_neg_d_q
  have hdq : jacobiSym (d : ℤ) q = -1 := by
    have h1 : jacobiSym (-(d : ℤ)) q = -jacobiSym (d : ℤ) q := by
      rw [jacobiSym.neg (d : ℤ) hH.odd_q, ZMod.χ₄_nat_three_mod_four hq4]
      ring
    linarith
  have hqd_sym : jacobiSym (q : ℤ) d = 1 := by
    have hrec := jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4
    linarith
  refine ⟨hH, hH.q_ne_two, hH.d_ne_two, hH.q_ne_d, hH.coprime_q_d,
    hneg_q, hneg_d, h2_q, h2_d, hneg_dq, hdq, hqd_sym, fun p hp hp2 hpn => ?_⟩
  exact HostFieldSupply.jacobiSym_neg_of_dvd_succ (hsmall p hp hp2 hpn)

/-- Concrete unconditional non-vacuity witness: `(3, 23)` satisfies `HostFieldSupply.HostHyp`. -/
theorem hostHyp_3_23 : HostFieldSupply.HostHyp 3 23 :=
  hostHyp_of_pairModEq (n := 2) (by norm_num) (by norm_num) (by norm_num) (by
    rw [pairModEq_iff (by norm_num) (by norm_num) (by norm_num)]
    refine ⟨by norm_num, by norm_num, fun p hp hp2 hle => ?_⟩
    have := hp.two_le; omega)

/-- Concrete unconditional witness with odd-primorial splitting up to `n = 5`:
`q = 11 ≡ 3 (mod 8)`, `d = 1319 ≡ 7 (mod 16)`, `11 ∣ 1320`, `3 ∣ 1320`, `5 ∣ 1320`. -/
theorem hostHyp_11_1319 :
    HostFieldSupply.HostHyp 11 1319 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ 5 → jacobiSym (-(1319 : ℤ)) p = 1) := by
  have hcongr : 1319 ≡ pairResidue 11 5 [MOD pairModulus 11 5] := by
    rw [pairModEq_iff (by norm_num) (by norm_num) (by norm_num)]
    refine ⟨by norm_num, by norm_num, fun p hp hp2 hle => ?_⟩
    have h2 : 2 ≤ p := hp.two_le
    have hcases : p = 3 ∨ p = 4 ∨ p = 5 := by omega
    rcases hcases with rfl | rfl | rfl
    · norm_num
    · exact absurd hp (by norm_num)
    · norm_num
  have hrec := reciprocity_of_pairModEq (q := 11) (n := 5) (d := 1319)
    (by norm_num) (by norm_num) (by norm_num) hcongr
  exact ⟨hrec.1, hrec.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Any prime `p > M` (with `0 < M`) is automatically coprime to `M`. -/
theorem coprime_of_prime_gt {M p : ℕ} (hM : 0 < M) (hp : p.Prime) (hlt : M < p) :
    Nat.Coprime M p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd =>
    absurd (Nat.le_of_dvd hM hdvd) (by omega)).symm

private theorem list_prod_mod_eight_eq_one {l : List ℕ} (hl : ∀ p ∈ l, p % 8 = 1) :
    l.prod % 8 = 1 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.prod_cons, Nat.mul_mod, hl a (by simp),
      ih fun p hp => hl p (by simp [hp])]

private theorem jacobiSym_neg_two_eq_one_imp_mod_eight {p : ℕ} (hp : Odd p)
    (h : jacobiSym (-2 : ℤ) p = 1) : p % 8 = 1 ∨ p % 8 = 3 := by
  have hsplit : jacobiSym (-2 : ℤ) p = jacobiSym (-1 : ℤ) p * jacobiSym (2 : ℤ) p := by
    rw [show (-2 : ℤ) = (-1 : ℤ) * 2 by norm_num, jacobiSym.mul_left]
  rw [hsplit, jacobiSym.at_neg_one hp, jacobiSym.at_two hp] at h
  have hodd : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have := Nat.odd_iff.mp hp
    omega
  rcases hodd with h1 | h3 | h5 | h7
  · exact Or.inl h1
  · exact Or.inr h3
  · exfalso
    have h4 : p % 4 = 1 := by omega
    have hχ4 : ZMod.χ₄ (p : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four h4
    have hχ8 : ZMod.χ₈ (p : ZMod 8) = -1 := by
      have : (p : ZMod 8) = (5 : ZMod 8) := by
        rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]
        change p % 8 = 5 % 8; omega
      rw [this]; decide
    rw [hχ4, hχ8] at h; norm_num at h
  · exfalso
    have h4 : p % 4 = 3 := by omega
    have hχ4 : ZMod.χ₄ (p : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four h4
    have hχ8 : ZMod.χ₈ (p : ZMod 8) = 1 := by
      have : (p : ZMod 8) = (7 : ZMod 8) := by
        rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]
        change p % 8 = 7 % 8; omega
      rw [this]; decide
    rw [hχ4, hχ8] at h; norm_num at h

private theorem jacobiSym_two_eq_one_imp_mod_eight {p : ℕ} (hp : Odd p)
    (h : jacobiSym (2 : ℤ) p = 1) : p % 8 = 1 ∨ p % 8 = 7 := by
  rw [jacobiSym.at_two hp] at h
  have hodd : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have := Nat.odd_iff.mp hp
    omega
  rcases hodd with h1 | h3 | h5 | h7
  · exact Or.inl h1
  · exfalso
    have : (p : ZMod 8) = (3 : ZMod 8) := by
      rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]
      change p % 8 = 3 % 8; omega
    rw [this] at h; revert h; decide
  · exfalso
    have : (p : ZMod 8) = (5 : ZMod 8) := by
      rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]
      change p % 8 = 5 % 8; omega
    rw [this] at h; revert h; decide
  · exact Or.inr h7

/-- **Unconditional Infinitude of Primes `q ≡ 3 (mod 8)`**:
Proved directly from scratch via `N = (oddPrimorial (max B 3)) ^ 2 + 2` and quadratic
reciprocity for `(-2 | p)`. -/
theorem exists_prime_gt_mod_eight_eq_three (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q % 8 = 3 := by
  set x := oddPrimorial (max B 3)
  set N := x ^ 2 + 2
  have hxodd : Odd x := odd_oddPrimorial (max B 3)
  have hN8 : N % 8 = 3 := by
    obtain ⟨k, hk⟩ := hxodd
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h8 : N = 8 * (2 * m ^ 2 + m) + 3 := by dsimp only [N]; rw [hk]; ring
      omega
    · have h8 : N = 8 * (2 * m ^ 2 + 3 * m + 1) + 3 := by dsimp only [N]; rw [hk]; ring
      omega
  have hNne : N ≠ 0 := by omega
  have hfac : ∀ p : ℕ, p.Prime → p ∣ N → B < p ∧ (p % 8 = 1 ∨ p % 8 = 3) := by
    intro p hp hpN
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpN
      omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have hndvd_x : ¬ p ∣ x := by
      intro hpx
      have h2 : p ∣ 2 := by
        have hsq : p ∣ x ^ 2 := dvd_pow hpx (by norm_num)
        exact (Nat.dvd_add_right hsq).mp hpN
      have := Nat.le_of_dvd (by norm_num) h2
      have := hp.two_le
      omega
    have hBp : B < p := by
      by_contra hle
      push Not at hle
      exact hndvd_x (dvd_oddPrimorial hp hp2 (hle.trans (le_max_left B 3)))
    have hmod : (-2 : ℤ) ≡ (x : ℤ) ^ 2 [ZMOD (p : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have h1 : (p : ℤ) ∣ ((x ^ 2 + 2 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpN
      push_cast at h1
      simpa [sub_neg_eq_add] using h1
    have hcop : Nat.Coprime x p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd_x |>.symm
    have hjac : jacobiSym (-2 : ℤ) p = 1 := by
      rw [jacobiSym.mod_left' hmod, jacobiSym.pow_left]
      rcases jacobiSym.eq_one_or_neg_one (a := (x : ℤ)) (b := p)
        (by rw [Int.gcd_natCast_natCast]; exact hcop) with h1 | h1 <;> rw [h1] <;> norm_num
    exact ⟨hBp, jacobiSym_neg_two_eq_one_imp_mod_eight hp_odd hjac⟩
  by_contra hno
  push Not at hno
  have hall1 : ∀ p ∈ N.primeFactorsList, p % 8 = 1 := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ N := Nat.dvd_of_mem_primeFactorsList hp
    obtain ⟨hBp, h1 | h3⟩ := hfac p hpr hdvd
    · exact h1
    · exact absurd h3 (hno p hBp hpr)
  have hprod := list_prod_mod_eight_eq_one hall1
  rw [Nat.prod_primeFactorsList hNne] at hprod
  omega

/-- **Unconditional Infinitude of Primes `q ≡ 3 (mod 8)` Coprime to Any `M > 0`**. -/
theorem exists_coprime_prime_mod_eight_eq_three (M B : ℕ) (hM : 0 < M) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q % 8 = 3 ∧ Nat.Coprime M q := by
  obtain ⟨q, hqB, hqp, hq8⟩ := exists_prime_gt_mod_eight_eq_three (max B M)
  exact ⟨q, lt_of_le_of_lt (le_max_left _ _) hqB, hqp, hq8,
    coprime_of_prime_gt hM hqp (lt_of_le_of_lt (le_max_right _ _) hqB)⟩

/-- **Unconditional Infinitude of Primes `d ≡ 7 (mod 8)`**:
Proved directly from scratch via `N = 2 * (2 * oddPrimorial (max B 2)) ^ 2 - 1` and
supplementary quadratic reciprocity for `(2 | p)`. -/
theorem exists_prime_gt_mod_eight_eq_seven (B : ℕ) :
    ∃ d : ℕ, B < d ∧ d.Prime ∧ d % 8 = 7 := by
  set y := oddPrimorial (max B 2)
  set x := 2 * y
  have hypos : 1 ≤ y := oddPrimorial_pos (max B 2)
  have hx2 : 2 ≤ x := by omega
  set N := 2 * x ^ 2 - 1
  have hN8 : N % 8 = 7 := by
    have h8 : 2 * x ^ 2 = 8 * y ^ 2 := by dsimp only [x]; ring
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    omega
  have hNne : N ≠ 0 := by omega
  have hfac : ∀ p : ℕ, p.Prime → p ∣ N → B < p ∧ (p % 8 = 1 ∨ p % 8 = 7) := by
    intro p hp hpN
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpN
      omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have hndvd_x : ¬ p ∣ x := by
      intro hpx
      have hsq : p ∣ 2 * x ^ 2 := (dvd_pow hpx (by norm_num)).trans (dvd_mul_left _ 2)
      have h1 : p ∣ 1 := by
        have hsub := Nat.dvd_sub hsq hpN
        have h1x : 1 ≤ 2 * x ^ 2 := by nlinarith
        have heq : 2 * x ^ 2 - (2 * x ^ 2 - 1) = 1 := by omega
        rwa [heq] at hsub
      exact absurd (Nat.dvd_one.mp h1) hp.ne_one
    have hBp : B < p := by
      by_contra hle
      push Not at hle
      have hpy : p ∣ y := dvd_oddPrimorial hp hp2 (hle.trans (le_max_left B 2))
      exact hndvd_x (hpy.trans (dvd_mul_left y 2))
    have hmod : (2 : ℤ) ≡ ((2 * x : ℕ) : ℤ) ^ 2 [ZMOD (p : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have h1 : (p : ℤ) ∣ ((2 * N : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (hpN.trans (dvd_mul_left N 2))
      have h2N : (2 * N : ℕ) + 2 = (2 * x) ^ 2 := by
        have h1x : 1 ≤ 2 * x ^ 2 := by nlinarith
        have hsq : (2 * x) ^ 2 = 2 * (2 * x ^ 2) := by ring
        dsimp only [N]
        omega
      have h2Nz : ((2 * x : ℕ) : ℤ) ^ 2 - 2 = ((2 * N : ℕ) : ℤ) := by
        have : (((2 * N : ℕ) + 2 : ℕ) : ℤ) = (((2 * x) ^ 2 : ℕ) : ℤ) := by exact_mod_cast h2N
        push_cast at this ⊢
        linarith
      rwa [h2Nz]
    have hcop : Nat.Coprime (2 * x) p :=
      (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd_x |>.symm))
    have hjac : jacobiSym (2 : ℤ) p = 1 := by
      rw [jacobiSym.mod_left' hmod, jacobiSym.pow_left]
      rcases jacobiSym.eq_one_or_neg_one (a := ((2 * x : ℕ) : ℤ)) (b := p)
        (by rw [Int.gcd_natCast_natCast]; exact hcop) with h1 | h1 <;> rw [h1] <;> norm_num
    exact ⟨hBp, jacobiSym_two_eq_one_imp_mod_eight hp_odd hjac⟩
  by_contra hno
  push Not at hno
  have hall1 : ∀ p ∈ N.primeFactorsList, p % 8 = 1 := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ N := Nat.dvd_of_mem_primeFactorsList hp
    obtain ⟨hBp, h1 | h7⟩ := hfac p hpr hdvd
    · exact h1
    · exact absurd h7 (hno p hBp hpr)
  have hprod := list_prod_mod_eight_eq_one hall1
  rw [Nat.prod_primeFactorsList hNne] at hprod
  omega

/-! ## Section 3: Unconditional Quantitative Modulus & Size Envelope -/

/-- Elementary exponential dominance `U ≤ exp (U / 2)` for all `U ≥ 0`. -/
theorem self_le_exp_half {U : ℝ} (hU : 0 ≤ U) : U ≤ Real.exp (U / 2) := by
  have h1 : U / 4 + 1 ≤ Real.exp (U / 4) := by linarith [Real.add_one_le_exp (U / 4)]
  have h2 : (U / 4 + 1) ^ 2 ≤ Real.exp (U / 4) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h1 2
  have h3 : Real.exp (U / 4) ^ 2 = Real.exp (U / 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h4 : U ≤ (U / 4 + 1) ^ 2 := by nlinarith [sq_nonneg (U / 4 - 1)]
  linarith

/-- Any positive integer `q` with `U / 2 < log q` automatically satisfies `⌊U⌋₊ < q`. -/
theorem floor_lt_of_half_lt_log {U : ℝ} {q : ℕ} (hU : 0 ≤ U) (hq : 0 < q)
    (hlo : U / 2 < Real.log (q : ℝ)) : ⌊U⌋₊ < q := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : Real.exp (U / 2) < (q : ℝ) := (Real.lt_log_iff_exp_lt hqpos).mp hlo
  have hfl : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le hU
  have hlt : (⌊U⌋₊ : ℝ) < (q : ℝ) := lt_of_le_of_lt (hfl.trans (self_le_exp_half hU)) hexp
  exact_mod_cast hlt

/-- Unconditional exponential bound on the odd primorial: `oddPrimorial ⌊U⌋₊ ≤ exp (2 * U)`. -/
theorem oddPrimorial_le_exp_two_mul {U : ℝ} (hU : 0 ≤ U) :
    (oddPrimorial ⌊U⌋₊ : ℝ) ≤ Real.exp (2 * U) := by
  have h1 : (oddPrimorial ⌊U⌋₊ : ℝ) ≤ (4 : ℝ) ^ ⌊U⌋₊ := by
    exact_mod_cast oddPrimorial_le_four_pow ⌊U⌋₊
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have he := Real.exp_one_gt_d9
    have hsq : Real.exp 1 ^ 2 = Real.exp 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    nlinarith
  have h2 : (4 : ℝ) ^ ⌊U⌋₊ ≤ (Real.exp 2) ^ ⌊U⌋₊ :=
    pow_le_pow_left₀ (by norm_num) h4 _
  have h3 : (Real.exp 2) ^ ⌊U⌋₊ = Real.exp (2 * (⌊U⌋₊ : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hfl : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le hU
  exact (h1.trans h2).trans (by rw [h3]; exact Real.exp_le_exp.mpr (by linarith))

/-- Unconditional quantitative modulus bound:
for `3 ≤ U` and `log q ≤ U`, the CRT modulus satisfies `pairModulus q ⌊U⌋₊ ≤ exp (4 * U)`. -/
theorem pairModulus_le_exp_four_mul {U : ℝ} {q : ℕ} (hU : 3 ≤ U) (hq : 0 < q)
    (hup : Real.log (q : ℝ) ≤ U) :
    (pairModulus q ⌊U⌋₊ : ℝ) ≤ Real.exp (4 * U) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqexp : (q : ℝ) ≤ Real.exp U := (Real.log_le_iff_le_exp hqpos).mp hup
  have hPexp : (oddPrimorial ⌊U⌋₊ : ℝ) ≤ Real.exp (2 * U) :=
    oddPrimorial_le_exp_two_mul (by linarith)
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by
    have he := Real.exp_one_gt_d9
    have hcube : Real.exp 1 ^ 3 = Real.exp 3 := by
      rw [pow_succ, sq, ← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith [sq_nonneg (Real.exp 1)]
  have hmul : (pairModulus q ⌊U⌋₊ : ℝ) = (16 : ℝ) * ((q : ℝ) * (oddPrimorial ⌊U⌋₊ : ℝ)) := by
    unfold pairModulus; push_cast; ring
  rw [hmul]
  have hqP : (q : ℝ) * (oddPrimorial ⌊U⌋₊ : ℝ) ≤ Real.exp U * Real.exp (2 * U) :=
    mul_le_mul hqexp hPexp (Nat.cast_nonneg _) (Real.exp_pos _).le
  calc (16 : ℝ) * ((q : ℝ) * (oddPrimorial ⌊U⌋₊ : ℝ))
      ≤ Real.exp 3 * (Real.exp U * Real.exp (2 * U)) :=
        mul_le_mul h16 hqP (by positivity) (Real.exp_pos _).le
    _ = Real.exp (3 + (U + 2 * U)) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (4 * U) := Real.exp_le_exp.mpr (by linarith)

/-- Unconditional Linnik-power modulus bound:
`(pairModulus q ⌊U⌋₊ : ℝ) ^ L ≤ exp (4 * L * U)` for `3 ≤ U`, `0 ≤ L`, `log q ≤ U`. -/
theorem pairModulus_rpow_le_exp {U L : ℝ} {q : ℕ} (hU : 3 ≤ U) (hL : 0 ≤ L) (hq : 0 < q)
    (hup : Real.log (q : ℝ) ≤ U) :
    (pairModulus q ⌊U⌋₊ : ℝ) ^ L ≤ Real.exp (4 * L * U) := by
  have hle := pairModulus_le_exp_four_mul hU hq hup
  calc (pairModulus q ⌊U⌋₊ : ℝ) ^ L
      ≤ (Real.exp (4 * U)) ^ L := Real.rpow_le_rpow (Nat.cast_nonneg _) hle hL
    _ = Real.exp (4 * L * U) := by rw [← Real.exp_mul]; congr 1; ring

/-- **Unconditional Assembly of `RHDirect.WinPair`**:
Assembles all 10 fields of `WinPair eps Y q d` directly from the two prime-in-AP witnesses
`q ≡ 3 [MOD 8]` in `(exp(U/2), exp(U)]` and `d ≡ pairResidue q ⌊U⌋₊ [MOD pairModulus q ⌊U⌋₊]`
in `(exp(V/2), exp(V)]`. -/
theorem winPair_of_congr_and_bounds {eps Y : ℝ} {q d : ℕ}
    (hq : q.Prime) (hq_mod : q ≡ 3 [MOD 8])
    (hq_lo : Real.exp (Y ^ (eps / 5) / 2) < (q : ℝ))
    (hq_up : (q : ℝ) ≤ Real.exp (Y ^ (eps / 5)))
    (hd : d.Prime)
    (hd_mod : d ≡ pairResidue q ⌊Y ^ (eps / 5)⌋₊ [MOD pairModulus q ⌊Y ^ (eps / 5)⌋₊])
    (hd_lo : Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2 / 2) < (d : ℝ))
    (hd_up : (d : ℝ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2)) :
    WinPair eps Y q d := by
  have hq8 : q % 8 = 3 := hq_mod
  obtain ⟨hd16, hqd, hsmall⟩ := pairModEq_imp hq8 hd_mod
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.pos
  refine
    { q_prime := hq
      q_mod := hq8
      q_lo := (Real.lt_log_iff_exp_lt hqpos).mpr hq_lo
      q_up := (Real.log_le_iff_le_exp hqpos).mpr hq_up
      d_prime := hd
      d_mod := hd16
      d_lo := (Real.lt_log_iff_exp_lt hdpos).mpr hd_lo
      d_up := (Real.log_le_iff_le_exp hdpos).mpr hd_up
      d_q := hqd
      d_small := fun p hp hp2 hpU => hsmall p hp hp2 (Nat.le_floor hpU) }

/-! ## Section 4: Exact 1-Line Linnik Prime-in-AP Reduction (`PairSupply`, `PairEx`, `SmallOne`) -/

/-- **Single 1-Line Analytic Number Theory Input (`LinnikAPInterval`)**:
There exists a Linnik exponent `L ≥ 1` such that for every modulus `m ≥ 2`, every residue
`a` coprime to `m`, and every scale `X ≥ m ^ L`, there exists a prime `p ≡ a [MOD m]` with
`X < p ≤ X ^ 2`.

This is a classical unconditional theorem of Linnik (1944), Fogels (1965), and Gallagher (1970)
(which in fact holds in the strictly tighter dyadic interval `(X, 2 * X]`, `LinnikAPDyadic`). -/
def LinnikAPInterval : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
    ∀ X : ℝ, (m : ℝ) ^ L ≤ X →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD m] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ X ^ 2

/-- Tighter dyadic Linnik/Fogels/Gallagher prime-in-AP predicate (`X < p ≤ 2 * X`). -/
def LinnikAPDyadic : Prop :=
  ∃ L : ℝ, 1 ≤ L ∧ ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
    ∀ X : ℝ, (m : ℝ) ^ L ≤ X →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD m] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ 2 * X

/-- `LinnikAPDyadic` immediately implies `LinnikAPInterval` (since `X ≥ m ^ L ≥ 2 ⇒ 2 * X ≤ X ^ 2`). -/
theorem linnikAPInterval_of_dyadic (h : LinnikAPDyadic) : LinnikAPInterval := by
  obtain ⟨L, hL1, hL⟩ := h
  refine ⟨L, hL1, fun m a hm hcop X hX => ?_⟩
  obtain ⟨p, hp, hmod, hlo, hup⟩ := hL m a hm hcop X hX
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2X : (2 : ℝ) ≤ X := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (m : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hm2 (by norm_num)
      _ ≤ (m : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le (by linarith) hL1
      _ ≤ X := hX
  exact ⟨p, hp, hmod, hlo, hup.trans (by nlinarith)⟩

/-- **Exact Discharge of `HostFieldSupply.SmallOne` from `LinnikAPInterval`**:
Taking `a = 1`, `X = M ^ L` produces `p ≡ 1 (mod M)` with `p ≤ M ^ (2 * L)`. -/
theorem smallOne_of_linnikAPInterval (h : LinnikAPInterval) : HostFieldSupply.SmallOne := by
  obtain ⟨L, hL1, hL⟩ := h
  refine ⟨2 * L, by linarith, fun M hM => ?_⟩
  obtain ⟨p, hp, hmod, _, hup⟩ := hL M 1 hM (Nat.coprime_one_left M) ((M : ℝ) ^ L) le_rfl
  have hM1 : 1 < M := by omega
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpm : p % M = 1 := by
    have : 1 % M = 1 := Nat.mod_eq_of_lt hM1
    exact Eq.trans hmod this
  refine ⟨p, hp, hpm, hup.trans_eq ?_⟩
  rw [sq, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < M))]
  congr 1
  ring

/-- **Direct Discharge of `exists_three_primes_one_mod_le_rpow` from `LinnikAPInterval`**. -/
theorem exists_three_primes_of_linnikAPInterval (h : LinnikAPInterval) :
    ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N →
      ∃ p p' q0 : ℕ,
        p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
        p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧
        (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 :=
  HostFieldSupply.exists_three_primes_one_mod_le_rpow (smallOne_of_linnikAPInterval h)

/-- **Master Reduction (`LinnikAPInterval → HostFieldSupply.PairSupply`)**:
Completely discharges `HostFieldSupply.PairSupply` (all congruence, CRT, odd-primorial,
reciprocity, distinctness, coprimality to `M`, and exponential-window constraints) from the
single 1-line Linnik prime-in-AP predicate `LinnikAPInterval`. -/
theorem pairSupply_of_linnikAPInterval (hLinnik : LinnikAPInterval) :
    HostFieldSupply.PairSupply := by
  obtain ⟨L, hL1, hL⟩ := hLinnik
  intro M hM eps _A heps _heps52 _hA
  have heps5 : 0 < eps / 5 := by linarith
  set U0 : ℝ := max 3 (max (2 * L * Real.log 8) (2 * Real.log ((M : ℝ) + 1)))
  have hU0_3 : 3 ≤ U0 := le_max_left _ _
  have hU0_8 : 2 * L * Real.log 8 ≤ U0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hU0_M : 2 * Real.log ((M : ℝ) + 1) ≤ U0 := le_trans (le_max_right _ _) (le_max_right _ _)
  have hU0_nn : 0 ≤ U0 := by linarith
  set Y1 : ℝ := max (Real.exp (8 * L + 1)) (U0 ^ (5 / eps))
  refine ⟨Y1, fun Y hY => ?_⟩
  have hY_exp : Real.exp (8 * L + 1) ≤ Y := le_trans (le_max_left _ _) hY
  have hY_U0 : U0 ^ (5 / eps) ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY_exp
  have hlogY_ge : 8 * L + 1 ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hY_exp
  have hlogY_1 : 1 ≤ Real.log Y := by linarith
  have hlogY_sq : 8 * L ≤ Real.log Y ^ 2 := by nlinarith
  set U : ℝ := Y ^ (eps / 5)
  have hU_ge_U0 : U0 ≤ U := by
    have hinv : (U0 ^ (5 / eps)) ^ (eps / 5) = U0 := by
      rw [← Real.rpow_mul hU0_nn]
      have h1 : 5 / eps * (eps / 5) = 1 := by field_simp [heps.ne']
      rw [h1, Real.rpow_one]
    calc U0 = (U0 ^ (5 / eps)) ^ (eps / 5) := hinv.symm
      _ ≤ Y ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg hU0_nn _) hY_U0 heps5.le
  have hU3 : 3 ≤ U := hU0_3.trans hU_ge_U0
  have hUpos : 0 < U := by linarith
  -- Step 1: Obtain auxiliary prime `q ≡ 3 (mod 8)` in `(exp(U/2), exp(U)]`.
  have h8L : ((8 : ℕ) : ℝ) ^ L ≤ Real.exp (U / 2) := by
    rw [Nat.cast_ofNat, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8)]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨q, hq_prime, hq_mod, hq_lo, hq_up'⟩ :=
    hL 8 3 (by norm_num) (by decide) (Real.exp (U / 2)) h8L
  have hq_up : (q : ℝ) ≤ Real.exp U := by
    refine hq_up'.trans_eq ?_
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hq_log_up : Real.log (q : ℝ) ≤ U :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hq_prime.pos)).mpr hq_up
  have hM_lt_expU2 : (M : ℝ) < Real.exp (U / 2) := by
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hle : (M : ℝ) + 1 ≤ Real.exp (U / 2) := by
      rw [← Real.exp_log hM1]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hMq : Nat.Coprime M q :=
    coprime_of_prime_gt hM hq_prime (by exact_mod_cast hM_lt_expU2.trans hq_lo)
  -- Step 2: Obtain auxiliary prime `d ≡ pairResidue q ⌊U⌋₊ [MOD pairModulus q ⌊U⌋₊]`
  -- in `(exp(V/2), exp(V)]` where `V = U * (log Y)^2`.
  set V : ℝ := U * Real.log Y ^ 2
  set n : ℕ := ⌊U⌋₊
  have hq8 : q % 8 = 3 := hq_mod
  have hKL : (pairModulus q n : ℝ) ^ L ≤ Real.exp (V / 2) := by
    calc (pairModulus q n : ℝ) ^ L
        ≤ Real.exp (4 * L * U) :=
          pairModulus_rpow_le_exp hU3 (by linarith) hq_prime.pos hq_log_up
      _ ≤ Real.exp (V / 2) := by
          apply Real.exp_le_exp.mpr
          dsimp only [V]
          nlinarith
  obtain ⟨d, hd_prime, hd_mod, hd_lo, hd_up'⟩ :=
    hL (pairModulus q n) (pairResidue q n)
      (two_le_pairModulus hq8) (coprime_pairResidue_pairModulus hq8) (Real.exp (V / 2)) hKL
  have hd_up : (d : ℝ) ≤ Real.exp V := by
    refine hd_up'.trans_eq ?_
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hUV : U / 2 ≤ V / 2 := by
    dsimp only [V]
    nlinarith [sq_nonneg (Real.log Y - 1)]
  have hMd : Nat.Coprime M d :=
    coprime_of_prime_gt hM hd_prime
      (by exact_mod_cast (hM_lt_expU2.trans_le (Real.exp_le_exp.mpr hUV)).trans hd_lo)
  exact ⟨q, d,
    winPair_of_congr_and_bounds hq_prime hq_mod hq_lo hq_up hd_prime hd_mod hd_lo hd_up,
    hMq.mul_right hMd⟩

/-- `HostFieldSupply.PairSupply` directly implies `ThetaSlopeEngine.PairEx`. -/
theorem pairEx_of_pairSupply (hPS : HostFieldSupply.PairSupply) : ThetaSlopeEngine.PairEx := by
  intro eps heps heps52
  obtain ⟨Y1, hY1⟩ := hPS 1 one_pos eps 1 heps heps52 le_rfl
  exact ⟨Y1, fun Y hY => let ⟨q, d, hpair, _⟩ := hY1 Y hY; ⟨q, d, hpair⟩⟩

/-- **Unconditional Converse (`ThetaSlopeEngine.PairEx → HostFieldSupply.PairSupply`)**:
The coprimality condition `Nat.Coprime M (q * d)` in `PairSupply` is completely automatic
from `WinPair`'s exponential lower bounds `Y ^ (eps / 5) / 2 < log q, log d` once `Y` is
large enough that `log (M + 1) ≤ Y ^ (eps / 5) / 2`. -/
theorem pairSupply_of_pairEx (hPE : ThetaSlopeEngine.PairEx) : HostFieldSupply.PairSupply := by
  intro M hM eps _A heps heps52 _hA
  obtain ⟨Y0, hY0⟩ := hPE eps heps heps52
  have heps5 : 0 < eps / 5 := by linarith
  set U0 : ℝ := max 1 (2 * Real.log ((M : ℝ) + 1))
  have hU0_nn : 0 ≤ U0 := le_trans (by norm_num) (le_max_left _ _)
  set Y1 : ℝ := max Y0 (max (Real.exp 1) (U0 ^ (5 / eps)))
  refine ⟨Y1, fun Y hY => ?_⟩
  have hY_Y0 : Y0 ≤ Y := le_trans (le_max_left _ _) hY
  have hY_exp : Real.exp 1 ≤ Y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hY)
  have hY_U0 : U0 ^ (5 / eps) ≤ Y := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hY)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hY_exp
  have hlogY : 1 ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hY_exp
  have hU_ge_U0 : U0 ≤ Y ^ (eps / 5) := by
    have hinv : (U0 ^ (5 / eps)) ^ (eps / 5) = U0 := by
      rw [← Real.rpow_mul hU0_nn]
      have h1 : 5 / eps * (eps / 5) = 1 := by field_simp [heps.ne']
      rw [h1, Real.rpow_one]
    calc U0 = (U0 ^ (5 / eps)) ^ (eps / 5) := hinv.symm
      _ ≤ Y ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg hU0_nn _) hY_U0 heps5.le
  obtain ⟨q, d, hw⟩ := hY0 Y hY_Y0
  have hM1pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hlogM_le : Real.log ((M : ℝ) + 1) ≤ Y ^ (eps / 5) / 2 := by
    have h1 : 2 * Real.log ((M : ℝ) + 1) ≤ U0 := le_max_right _ _
    linarith
  have hM_lt_q : M < q := by
    have hlt : Real.log ((M : ℝ) + 1) < Real.log (q : ℝ) := lt_of_le_of_lt hlogM_le hw.q_lo
    have hR : (M : ℝ) + 1 < (q : ℝ) :=
      (Real.log_lt_log_iff hM1pos (by exact_mod_cast hw.q_prime.pos)).mp hlt
    exact_mod_cast (by linarith : (M : ℝ) < (q : ℝ))
  have hM_lt_d : M < d := by
    have hUpos : 0 ≤ Y ^ (eps / 5) := Real.rpow_nonneg hYpos.le _
    have hUV : Y ^ (eps / 5) / 2 ≤ Y ^ (eps / 5) * Real.log Y ^ 2 / 2 := by
      nlinarith [sq_nonneg (Real.log Y - 1)]
    have hlt : Real.log ((M : ℝ) + 1) < Real.log (d : ℝ) :=
      lt_of_le_of_lt (hlogM_le.trans hUV) hw.d_lo
    have hR : (M : ℝ) + 1 < (d : ℝ) :=
      (Real.log_lt_log_iff hM1pos (by exact_mod_cast hw.d_prime.pos)).mp hlt
    exact_mod_cast (by linarith : (M : ℝ) < (d : ℝ))
  exact ⟨q, d, hw,
    (coprime_of_prime_gt hM hw.q_prime hM_lt_q).mul_right
      (coprime_of_prime_gt hM hw.d_prime hM_lt_d)⟩

/-- **Exact Equivalence**: `HostFieldSupply.PairSupply ↔ ThetaSlopeEngine.PairEx`. -/
theorem pairSupply_iff_pairEx : HostFieldSupply.PairSupply ↔ ThetaSlopeEngine.PairEx :=
  ⟨pairEx_of_pairSupply, pairSupply_of_pairEx⟩

/-- **Master Reduction (`LinnikAPInterval → ThetaSlopeEngine.PairEx`)**. -/
theorem pairEx_of_linnikAPInterval (hLinnik : LinnikAPInterval) : ThetaSlopeEngine.PairEx :=
  pairEx_of_pairSupply (pairSupply_of_linnikAPInterval hLinnik)

/-- Dyadic corollary: `LinnikAPDyadic → HostFieldSupply.PairSupply`. -/
theorem pairSupply_of_linnikAPDyadic (h : LinnikAPDyadic) : HostFieldSupply.PairSupply :=
  pairSupply_of_linnikAPInterval (linnikAPInterval_of_dyadic h)

/-- Dyadic corollary: `LinnikAPDyadic → ThetaSlopeEngine.PairEx`. -/
theorem pairEx_of_linnikAPDyadic (h : LinnikAPDyadic) : ThetaSlopeEngine.PairEx :=
  pairEx_of_linnikAPInterval (linnikAPInterval_of_dyadic h)

/-- Drop-in window extraction directly from `LinnikAPInterval` (discharging `PairEx`). -/
theorem winPairs_of_vwinAt_of_linnikAPInterval (S : SelmerSystem) (ψ : PChar) (eps c : ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c)
    (hV : VWinAt S ψ 401) (hLinnik : LinnikAPInterval) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
      ∃ (Y : ℝ) (q d e : ℕ), ThetaSlopeEngine.WinDatum S ψ eps J c x Y q d e :=
  ThetaSlopeEngine.winPairs_of_vwinAt S ψ eps c heps heps52 hc hV
    (pairEx_of_linnikAPInterval hLinnik)

/-- Drop-in host-field supply assembly directly from `LinnikAPInterval`
(discharging `HostFieldSupply.PairSupply`). -/
theorem hostFieldSupply_assembly_of_linnikAPInterval (S : SelmerSystem) (ψ : PChar)
    (hV : VWinAt S ψ 401) (hLinnik : LinnikAPInterval) :
    ∃ c e0 : ℕ, 1 ≤ c ∧
      (∀ e ≥ e0, HostFieldSupply.towerOrd (Subgroup.zpowers ψ.χ) e = c * 2 ^ e ∧
        ψ.N ∣ HostFieldSupply.QS (Subgroup.zpowers ψ.χ) e ∧
        HostFieldSupply.QS (Subgroup.zpowers ψ.χ) e ≤ 4 * ψ.N * 2 ^ e) ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
        ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧
          ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
            ∃ (Y : ℝ) (q d e : ℕ),
              HostFieldSupply.WinDatum S ψ eps J (c : ℝ) x Y q d e ∧
                HostFieldSupply.HostHyp q d :=
  HostFieldSupply.hostFieldSupply_assembly S ψ hV (pairSupply_of_linnikAPInterval hLinnik)

/-- Discharges the `pairEx` field of `ThetaSlopeEngine.MinimalThetaEngineInputs S` directly
from `LinnikAPInterval`. -/
def minimalThetaEngineInputs_of_linnikAPInterval (S : SelmerSystem)
    (eD eL : ℝ) (heD : 0 ≤ eD) (heL : 0 ≤ eL)
    (hLinnik : LinnikAPInterval)
    (hRealize : ∀ (ψ : PChar) (eps J : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ J →
      ∃ X0 : ℝ, ∀ (x Y : ℝ) (q d e : ℕ), X0 ≤ x →
        ThetaSlopeEngine.WinDatum S ψ eps J 1 x Y q d e →
        ThetaSlopeEngine.ThetaSlopeFiberRealization ψ eD eL eps x) :
    ThetaSlopeEngine.MinimalThetaEngineInputs S where
  eD := eD
  eL := eL
  eD_nonneg := heD
  eL_nonneg := heL
  pairEx := pairEx_of_linnikAPInterval hLinnik
  realize := hRealize

end RHDirect.Stage2PrimePairs

end
