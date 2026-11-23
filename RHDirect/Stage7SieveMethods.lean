import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage2BehrendSieve
import RHDirect.Stage2DirichletAP
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# RHDirect.Stage7SieveMethods

Unconditional, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of:
1. **Montgomery's Arithmetic Large Sieve**:
   - Weighted prime-modulus Parseval + Cauchy–Schwarz lower bound on `ZMod p`.
   - Exact two-factor CRT splitting and inductive **Squarefree Multiplicative Lifting**:
     `(∏_{p ∣ q} ω(p) / (p - ω(p))) * |A|² ≤ ∑_{(a, q)=1} ‖S_A(a/q)‖²`.
   - Full **Montgomery Arithmetic Large Sieve** (`|A| * L(Q) ≤ N + 3 Q²` and
     `|A| ≤ (N + 3 Q²) / L(Q)`) via `Stage3BombieriVinogradov.farey_large_sieve_Ico`.
2. **Elementary Harmonic & Coprime Totient Lower Bounds**:
   - `log (Q + 1) ≤ ∑_{m ≤ Q} 1 / m ≤ ∑_{n ≤ Q, Squarefree n} 1 / φ(n)` via radical-fiber
     unique factorization and finite geometric series.
   - Coprime-to-`q` sieve-sum lower bound:
     `(φ(q) / q) * log (Q + 1) ≤ ∑_{n ≤ Q, Squarefree n, (n, q) = 1} 1 / φ(n)`.
3. **Unconditional Brun–Titchmarsh Prime Upper Bounds (Intervals & Arithmetic Progressions)**:
   - Raw Montgomery-sieve prime bound, explicit `≤ 5 * y / log y` (`9 ≤ y`), and sharp
     asymptotic `(2 + ε) * y / log y` (`brun_titchmarsh_primes`, `brun_titchmarsh_primes_sharp`).
   - Arithmetic progressions: explicit `≤ 10 * y / (φ(q) * log (y / q))` (`9 * q ≤ y`),
     bridge to `Stage2DirichletAP.primeCountAP`, and sharp asymptotic `(2 + ε) * y / (φ(q) * log (y / q))`
     (`brun_titchmarsh_ap`, `brun_titchmarsh_primeCountAP`, `brun_titchmarsh_ap_sharp`).
4. **Selberg's Optimal Upper-Bound Sieve (Möbius Diagonalization)**:
   - Exact diagonalization `∑_{d₁, d₂ ≤ z} λ_{d₁} λ_{d₂} g([d₁, d₂]) = ∑_{r ≤ z} y_r² / f(r)`.
   - Exact Möbius linear constraint `∑_{r ≤ z} y_r / f(r) = λ_1` and completing-the-square
     identity proving `1 / G(z)` is the exact unique minimum, realized by explicit optimal weights
     `λ*_d` with `|λ*_d| ≤ 1`.
   - Full **Selberg Upper-Bound Sieve** for any finite set `A : Finset ℕ`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace RHDirect
namespace Stage7SieveMethods

open Stage3BombieriVinogradov

/-! ## Section 1: Montgomery's Arithmetic Large Sieve -/

/-- Weighted exponential sum `∑_{n ∈ A} w(n) e(n α)`. -/
def expSum (A : Finset ℕ) (w : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ A, w n * e ((n : ℝ) * α)

/-- Unweighted indicator exponential sum `∑_{n ∈ A} e(n α)`. -/
def indExpSum (A : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ A, e ((n : ℝ) * α)

/-- Montgomery sieve weight `∏_{p ∣ q} ω(p) / (p - ω(p))` for squarefree `q`, and `0` otherwise. -/
def sieveWeight (ω : ℕ → ℕ) (q : ℕ) : ℝ :=
  if Squarefree q then
    ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ))
  else 0

/-- Montgomery sieve denominator `L(Q) = ∑_{1 ≤ q ≤ Q} sieveWeight ω q`. -/
def montgomeryL (ω : ℕ → ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, sieveWeight ω q

/-- Periodicity of `e (n * α)` under integer shifts of `α`. -/
private theorem e_nat_mul_add_int (n : ℕ) (α : ℝ) (k : ℤ) :
    e ((n : ℝ) * (α + (k : ℝ))) = e ((n : ℝ) * α) := by
  have h : (n : ℝ) * (α + (k : ℝ)) = (n : ℝ) * α - (((-(n : ℤ) * k : ℤ) : ℝ)) := by
    push_cast; ring
  rw [h, e_sub_int]

/-- **Exact Prime-Modulus Weighted Cauchy–Schwarz Lower Bound**:
for any prime `p`, finite set `A`, complex weights `w : ℕ → ℂ`, and forbidden residue set
`Ω ⊆ ZMod p` with `Ω.card < p` avoided by `A`,
`(Ω.card / (p - Ω.card)) * ‖∑_{n ∈ A} w n‖² ≤ ∑_{a < p, (a, p) = 1} ‖∑_{n ∈ A} w n e(n a / p)‖²`. -/
theorem prime_modulus_weighted_lower_bound {p : ℕ} (hp : p.Prime) (A : Finset ℕ) (w : ℕ → ℂ)
    (Ω : Finset (ZMod p)) (hΩ_lt : Ω.card < p)
    (hAvoid : ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    ((Ω.card : ℝ) / ((p : ℝ) - (Ω.card : ℝ))) * ‖∑ n ∈ A, w n‖ ^ 2 ≤
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
        ‖expSum A w ((a : ℝ) / (p : ℝ))‖ ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let Φ : ZMod p → ℂ := fun r => ∑ n ∈ A.filter (fun n : ℕ => (n : ZMod p) = r), w n
  have hdft : ∀ k : ZMod p,
      ZMod.dft Φ (-k) = expSum A w ((k.val : ℝ) / (p : ℝ)) := by
    intro k
    rw [ZMod.dft_def]
    simp only [smul_eq_mul, Φ, Finset.mul_sum]
    have hsum : ∑ j : ZMod p, ∑ n ∈ A.filter (fun n : ℕ => (n : ZMod p) = j),
        ZMod.stdAddChar (-(j * -k)) * w n =
        ∑ n ∈ A, ZMod.stdAddChar ((n : ZMod p) * k) * w n := by
      have h1 : ∀ j : ZMod p,
          ∑ n ∈ A.filter (fun n : ℕ => (n : ZMod p) = j), ZMod.stdAddChar (-(j * -k)) * w n =
          ∑ n ∈ A.filter (fun n : ℕ => (n : ZMod p) = j), ZMod.stdAddChar ((n : ZMod p) * k) * w n := by
        intro j
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [(Finset.mem_filter.mp hn).2, mul_neg, neg_neg]
      simp_rw [h1]
      exact Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p))
        (fun _ _ => Finset.mem_univ _) _
    rw [hsum]
    unfold expSum
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_comm]
    congr 1
    have hmul : (n : ZMod p) * k = ((n * k.val : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hmul, stdAddChar_natCast_eq_e]
    congr 1
    push_cast
    ring
  have hparseval : ∑ k : ZMod p, ‖expSum A w ((k.val : ℝ) / (p : ℝ))‖ ^ 2 =
      (p : ℝ) * ∑ r : ZMod p, ‖Φ r‖ ^ 2 := by
    have hneg := zmod_dft_parseval (q := p) Φ
    have hshift : ∑ k : ZMod p, ‖ZMod.dft Φ (-k)‖ ^ 2 = ∑ k : ZMod p, ‖ZMod.dft Φ k‖ ^ 2 :=
      Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun _ => rfl
    rw [← hshift] at hneg
    simp_rw [hdft] at hneg
    exact hneg
  have hsum_split : ∑ k : ZMod p, ‖expSum A w ((k.val : ℝ) / (p : ℝ))‖ ^ 2 =
      ‖∑ n ∈ A, w n‖ ^ 2 +
        ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
          ‖expSum A w ((a : ℝ) / (p : ℝ))‖ ^ 2 := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod p)) _ (Finset.mem_univ (0 : ZMod p))]
    congr 1
    · simp only [ZMod.val_zero, Nat.cast_zero, zero_div, expSum, mul_zero, e_zero, mul_one]
    · refine Finset.sum_bij (fun (k : ZMod p) _ => k.val) ?_ ?_ ?_ ?_
      · intro k hk
        have hne : k ≠ 0 := (Finset.mem_erase.mp hk).1
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt k), ?_⟩
        have hpos : 0 < k.val := Nat.pos_of_ne_zero fun h0 =>
          hne (by rw [← ZMod.natCast_zmod_val k, h0, Nat.cast_zero])
        exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos (ZMod.val_lt k))).symm
      · intro k₁ _ k₂ _ h
        rw [← ZMod.natCast_zmod_val k₁, ← ZMod.natCast_zmod_val k₂, h]
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        refine ⟨(a : ZMod p), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · intro h0
          have hdvd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
          have hcop : Nat.Coprime a p := ha.2
          have : p ∣ Nat.gcd a p := Nat.dvd_gcd hdvd dvd_rfl
          rw [hcop.gcd_eq_one] at this
          exact hp.ne_one (Nat.dvd_one.mp this)
        · simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
      · intro _ _; rfl
  let R : Finset (ZMod p) := Finset.univ \ Ω
  have hR_card : (R.card : ℝ) = (p : ℝ) - (Ω.card : ℝ) := by
    have hnat : R.card = p - Ω.card := by
      dsimp only [R]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Ω), Finset.card_univ, ZMod.card]
    rw [hnat, Nat.cast_sub (le_of_lt hΩ_lt)]
  have hΦ_zero : ∀ r ∈ Ω, Φ r = 0 := by
    intro r hr
    dsimp only [Φ]
    refine Finset.sum_eq_zero fun n hn => ?_
    exfalso
    have hmem := Finset.mem_filter.mp hn
    exact hAvoid n hmem.1 (hmem.2.symm ▸ hr)
  have hsum_A : ∑ n ∈ A, w n = ∑ r ∈ R, Φ r := by
    have hall : ∑ n ∈ A, w n = ∑ r : ZMod p, Φ r :=
      (Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p))
        (fun _ _ => Finset.mem_univ _) w).symm
    rw [hall]
    symm
    refine Finset.sum_subset (Finset.subset_univ R) fun r _ hrR => ?_
    have hrΩ : r ∈ Ω := by
      by_contra hnot
      exact hrR (Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hnot⟩)
    exact hΦ_zero r hrΩ
  have hCS : ‖∑ n ∈ A, w n‖ ^ 2 ≤ ((p : ℝ) - (Ω.card : ℝ)) * ∑ r : ZMod p, ‖Φ r‖ ^ 2 := by
    rw [hsum_A]
    calc ‖∑ r ∈ R, Φ r‖ ^ 2
        ≤ (R.card : ℝ) * ∑ r ∈ R, ‖Φ r‖ ^ 2 := Stage2BehrendSieve.cauchy_schwarz_complex_card R Φ
      _ = ((p : ℝ) - (Ω.card : ℝ)) * ∑ r ∈ R, ‖Φ r‖ ^ 2 := by rw [hR_card]
      _ ≤ ((p : ℝ) - (Ω.card : ℝ)) * ∑ r : ZMod p, ‖Φ r‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [(by exact_mod_cast hΩ_lt : (Ω.card : ℝ) < (p : ℝ))])
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun _ _ _ => sq_nonneg _
  have hden : (0 : ℝ) < (p : ℝ) - (Ω.card : ℝ) := by
    have : (Ω.card : ℝ) < (p : ℝ) := by exact_mod_cast hΩ_lt
    linarith
  have hmain : (p : ℝ) * ‖∑ n ∈ A, w n‖ ^ 2 ≤
      ((p : ℝ) - (Ω.card : ℝ)) * ((p : ℝ) * ∑ r : ZMod p, ‖Φ r‖ ^ 2) := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hCS hp0
    linarith
  rw [← hparseval, hsum_split] at hmain
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

/-- Prime-modulus lower bound for the indicator exponential sum `indExpSum A` over `Icc 1 (p - 1)`. -/
theorem prime_modulus_lower_bound {p : ℕ} (hp : p.Prime) (A : Finset ℕ)
    (Ω : Finset (ZMod p)) (hΩ_lt : Ω.card < p)
    (hAvoid : ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    ((Ω.card : ℝ) / ((p : ℝ) - (Ω.card : ℝ))) * (A.card : ℝ) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 (p - 1), ‖indExpSum A ((a : ℝ) / (p : ℝ))‖ ^ 2 := by
  have h := prime_modulus_weighted_lower_bound hp A (fun _ => (1 : ℂ)) Ω hΩ_lt hAvoid
  have hnorm : ‖∑ _n ∈ A, (1 : ℂ)‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    simp
  have hfilt : (Finset.range p).filter (fun a => Nat.Coprime a p) = Finset.Icc 1 (p - 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨ha, hcop⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [Nat.coprime_zero_left] at hcop
        exact hp.ne_one hcop
      omega
    · rintro ⟨h1, h2⟩
      have hlt : a < p := by have := hp.two_le; omega
      exact ⟨hlt, (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hlt)).symm⟩
  rw [hnorm, hfilt] at h
  refine h.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
  simp [expSum, indExpSum]

/-- Exact two-factor CRT splitting of reduced-residue exponential sums for coprime `p, m ≥ 1`. -/
theorem sum_reduced_residues_mul_coprime {p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hcop : Nat.Coprime p m) (A : Finset ℕ) (w : ℕ → ℂ) :
    ∑ a ∈ (Finset.range (p * m)).filter (fun a => Nat.Coprime a (p * m)),
        ‖expSum A w ((a : ℝ) / ((p * m : ℕ) : ℝ))‖ ^ 2 =
      ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
        ∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
          ‖expSum A (fun n => w n * e ((n : ℝ) * ((c : ℝ) / (m : ℝ)))) ((b : ℝ) / (p : ℝ))‖ ^ 2 := by
  have : NeZero p := ⟨hp.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩
  have hpm : 0 < p * m := Nat.mul_pos hp hm
  have hmodp_zmod : ∀ b c : ℕ, ((b * m + c * p) % (p * m) : ZMod p) = (b : ZMod p) * (m : ZMod p) := by
    intro b c
    have h1 : (b * m + c * p) % (p * m) % p = (b * m) % p := by
      rw [Nat.mod_mul_right_mod, Nat.add_mul_mod_self_right]
    have h2 : (((b * m + c * p) % (p * m) : ℕ) : ZMod p) = ((b * m : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ p).mpr h1
    rw [h2, Nat.cast_mul]
  have hmodm_zmod : ∀ b c : ℕ, ((b * m + c * p) % (p * m) : ZMod m) = (c : ZMod m) * (p : ZMod m) := by
    intro b c
    have h1 : (b * m + c * p) % (p * m) % m = (c * p) % m := by
      rw [Nat.mod_mul_left_mod, add_comm, Nat.add_mul_mod_self_right]
    have h2 : (((b * m + c * p) % (p * m) : ℕ) : ZMod m) = ((c * p : ℕ) : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff _ _ m).mpr h1
    rw [h2, Nat.cast_mul]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun bc _ => (bc.2 * m + bc.1 * p) % (p * m)) ?_ ?_ ?_ ?_
  · intro bc hbc
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hbc
    obtain ⟨⟨_, hc_cop⟩, ⟨_, hb_cop⟩⟩ := hbc
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hpm), ?_⟩
    have hcop_p : Nat.Coprime ((bc.2 * m + bc.1 * p) % (p * m)) p := by
      rw [← ZMod.isUnit_iff_coprime, hmodp_zmod]
      exact ((ZMod.isUnit_iff_coprime bc.2 p).mpr hb_cop).mul
        ((ZMod.isUnit_iff_coprime m p).mpr hcop.symm)
    have hcop_m : Nat.Coprime ((bc.2 * m + bc.1 * p) % (p * m)) m := by
      rw [← ZMod.isUnit_iff_coprime, hmodm_zmod]
      exact ((ZMod.isUnit_iff_coprime bc.1 m).mpr hc_cop).mul
        ((ZMod.isUnit_iff_coprime p m).mpr hcop)
    exact hcop_p.mul_right hcop_m
  · intro bc₁ hbc₁ bc₂ hbc₂ heq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hbc₁ hbc₂
    have hum : IsUnit (m : ZMod p) := (ZMod.isUnit_iff_coprime m p).mpr hcop.symm
    have hb_zmod : (bc₁.2 : ZMod p) = (bc₂.2 : ZMod p) := by
      have hmul : (bc₁.2 : ZMod p) * (m : ZMod p) = (bc₂.2 : ZMod p) * (m : ZMod p) := by
        rw [← hmodp_zmod, ← hmodp_zmod, heq]
      exact hum.mul_right_cancel hmul
    have hb_eq : bc₁.2 = bc₂.2 := by
      have h := congrArg ZMod.val hb_zmod
      rwa [ZMod.val_natCast_of_lt hbc₁.2.1, ZMod.val_natCast_of_lt hbc₂.2.1] at h
    have hup : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hcop
    have hc_zmod : (bc₁.1 : ZMod m) = (bc₂.1 : ZMod m) := by
      have hmul : (bc₁.1 : ZMod m) * (p : ZMod m) = (bc₂.1 : ZMod m) * (p : ZMod m) := by
        rw [← hmodm_zmod, ← hmodm_zmod, heq]
      exact hup.mul_right_cancel hmul
    have hc_eq : bc₁.1 = bc₂.1 := by
      have h := congrArg ZMod.val hc_zmod
      rwa [ZMod.val_natCast_of_lt hbc₁.1.1, ZMod.val_natCast_of_lt hbc₂.1.1] at h
    exact Prod.ext hc_eq hb_eq
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨ha_lt, ha_cop⟩ := ha
    have ha_p : Nat.Coprime a p := ha_cop.coprime_dvd_right (dvd_mul_right p m)
    have ha_m : Nat.Coprime a m := ha_cop.coprime_dvd_right (dvd_mul_left m p)
    have hum : IsUnit (m : ZMod p) := (ZMod.isUnit_iff_coprime m p).mpr hcop.symm
    have hup : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hcop
    let bZ : ZMod p := (a : ZMod p) * (hum.unit⁻¹ : (ZMod p)ˣ)
    let cZ : ZMod m := (a : ZMod m) * (hup.unit⁻¹ : (ZMod m)ˣ)
    refine ⟨(cZ.val, bZ.val), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨ZMod.val_lt cZ, ?_⟩, ⟨ZMod.val_lt bZ, ?_⟩⟩
      · have hcu : IsUnit ((cZ.val : ℕ) : ZMod m) := by
          rw [ZMod.natCast_zmod_val]
          exact ((ZMod.isUnit_iff_coprime a m).mpr ha_m).mul hup.unit⁻¹.isUnit
        exact (ZMod.isUnit_iff_coprime _ m).mp hcu
      · have hbu : IsUnit ((bZ.val : ℕ) : ZMod p) := by
          rw [ZMod.natCast_zmod_val]
          exact ((ZMod.isUnit_iff_coprime a p).mpr ha_p).mul hum.unit⁻¹.isUnit
        exact (ZMod.isUnit_iff_coprime _ p).mp hbu
    · have hmodp : bZ.val * m + cZ.val * p ≡ a [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero]
        dsimp only [bZ]
        rw [mul_assoc, show ((hum.unit⁻¹ : (ZMod p)ˣ) : ZMod p) * (m : ZMod p) = 1 by
          simp, mul_one]
      have hmodm : bZ.val * m + cZ.val * p ≡ a [MOD m] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, zero_add]
        dsimp only [cZ]
        rw [mul_assoc, show ((hup.unit⁻¹ : (ZMod m)ˣ) : ZMod m) * (p : ZMod m) = 1 by
          simp, mul_one]
      have hmodpm : bZ.val * m + cZ.val * p ≡ a [MOD p * m] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodp, hmodm⟩
      exact Eq.trans hmodpm (Nat.mod_eq_of_lt ha_lt)
  · intro bc _
    congr 2
    unfold expSum
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← e_add]
    congr 1
    set s : ℕ := bc.2 * m + bc.1 * p
    have hdiv : s = (p * m) * (s / (p * m)) + s % (p * m) := (Nat.div_add_mod s (p * m)).symm
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
    have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have halpha : ((s % (p * m) : ℕ) : ℝ) / ((p * m : ℕ) : ℝ) + ((s / (p * m) : ℕ) : ℝ) =
        (bc.1 : ℝ) / (m : ℝ) + (bc.2 : ℝ) / (p : ℝ) := by
      have hsR : (s : ℝ) = ((p * m : ℕ) : ℝ) * ((s / (p * m) : ℕ) : ℝ) + ((s % (p * m) : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      have hsdef : (s : ℝ) = (bc.2 : ℝ) * (m : ℝ) + (bc.1 : ℝ) * (p : ℝ) := by
        dsimp only [s]; push_cast; ring
      have hpmne : ((p * m : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at hsR hpmne ⊢
      field_simp [hpR.ne', hmR.ne']
      linarith
    have he1 : e ((n : ℝ) * ((bc.1 : ℝ) / (m : ℝ)) + (n : ℝ) * ((bc.2 : ℝ) / (p : ℝ))) =
        e ((n : ℝ) * (((s % (p * m) : ℕ) : ℝ) / ((p * m : ℕ) : ℝ) + ((s / (p * m) : ℕ) : ℤ))) := by
      congr 1
      have hcast : ((s / (p * m) : ℕ) : ℝ) = (((s / (p * m) : ℕ) : ℤ) : ℝ) :=
        (Int.cast_natCast (s / (p * m))).symm
      rw [← hcast, halpha]; ring
    rw [he1, e_nat_mul_add_int]

/-- **Exact Squarefree Multiplicative Lifting (CRT Induction)**:
for any squarefree `q ≥ 1` and finite `A : Finset ℕ` avoiding `ω(p) < p` residue classes modulo
every prime `p ∣ q`,
`(∏_{p ∣ q} ω(p) / (p - ω(p))) * |A|² ≤ ∑_{a < q, (a, q) = 1} ‖S_A(a/q)‖²`. -/
theorem squarefree_multiplicative_lifting_weighted {q : ℕ} (hq : Squarefree q) (A : Finset ℕ)
    (w : ℕ → ℂ) (ω : ℕ → ℕ)
    (hAvoid : ∀ p ∈ q.primeFactors,
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    (∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ))) * ‖∑ n ∈ A, w n‖ ^ 2 ≤
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖expSum A w ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
  induction q using Nat.strong_induction_on generalizing w with
  | _ q ih =>
    have hq_ne : q ≠ 0 := hq.ne_zero
    by_cases hq1 : q = 1
    · subst hq1
      have hfilt : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
          Nat.coprime_one_right_eq_true, and_true]; omega
      rw [hfilt, Finset.sum_singleton]
      simp [expSum, e_zero]
    · set p : ℕ := q.minFac
      have hp : p.Prime := Nat.minFac_prime hq1
      have hp_dvd : p ∣ q := Nat.minFac_dvd q
      set m : ℕ := q / p
      have hqm : q = p * m := (Nat.mul_div_cancel' hp_dvd).symm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by rw [hm0, mul_zero] at hqm; exact hq_ne hqm
      have hm_lt : m < q := by
        have := hp.two_le
        nlinarith
      have hndvd : ¬ p ∣ m := by
        intro hpm
        have hsq : p * p ∣ q := by
          obtain ⟨k, hk⟩ := hpm
          exact ⟨k, by rw [hqm, hk]; ring⟩
        exact hp.ne_one (Nat.isUnit_iff.mp (hq p hsq))
      have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hndvd
      have hm_sqf : Squarefree m := hq.squarefree_of_dvd ⟨p, by rw [hqm, mul_comm]⟩
      have hp_mem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hq_ne⟩
      have hp_not_m : p ∉ m.primeFactors := fun h => hndvd (Nat.dvd_of_mem_primeFactors h)
      have hpf_eq : q.primeFactors = insert p m.primeFactors := by
        ext r
        simp only [Nat.mem_primeFactors, Finset.mem_insert]
        constructor
        · rintro ⟨hr, hrdvd, -⟩
          rw [hqm] at hrdvd
          rcases hr.dvd_mul.mp hrdvd with hrp | hrm
          · left; exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
          · right; exact ⟨hr, hrm, hm_pos.ne'⟩
        · rintro (rfl | ⟨hr, hrm, -⟩)
          · exact ⟨hp, hp_dvd, hq_ne⟩
          · exact ⟨hr, hrm.trans ⟨p, by rw [hqm, mul_comm]⟩, hq_ne⟩
      obtain ⟨hω_lt, Ω, hΩ_card, hΩ_avoid⟩ := hAvoid p hp_mem
      have hm_avoid : ∀ r ∈ m.primeFactors,
          ω r < r ∧ ∃ Ω' : Finset (ZMod r), Ω'.card = ω r ∧ ∀ n ∈ A, (n : ZMod r) ∉ Ω' := by
        intro r hr
        exact hAvoid r (by rw [hpf_eq]; exact Finset.mem_insert_of_mem hr)
      have hsplit := sum_reduced_residues_mul_coprime hp.pos hm_pos hcop A w
      rw [hqm]
      rw [hsplit]
      have hstep :
          ((ω p : ℝ) / ((p : ℝ) - (ω p : ℝ))) *
            ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
              ‖expSum A w ((c : ℝ) / (m : ℝ))‖ ^ 2 ≤
          ∑ c ∈ (Finset.range m).filter (fun c => Nat.Coprime c m),
            ∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
              ‖expSum A (fun n => w n * e ((n : ℝ) * ((c : ℝ) / (m : ℝ)))) ((b : ℝ) / (p : ℝ))‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have hpm_lb := prime_modulus_weighted_lower_bound hp A
          (fun n => w n * e ((n : ℝ) * ((c : ℝ) / (m : ℝ)))) Ω (hΩ_card.symm ▸ hω_lt) hΩ_avoid
        simpa [hΩ_card, expSum] using hpm_lb
      have hfactor_nn : 0 ≤ (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) := by
        have hlt : (ω p : ℝ) < (p : ℝ) := by exact_mod_cast hω_lt
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      have hih := ih m hm_lt hm_sqf w hm_avoid
      rw [← hqm, hpf_eq, Finset.prod_insert hp_not_m, mul_assoc]
      exact (mul_le_mul_of_nonneg_left hih hfactor_nn).trans hstep

/-- Unweighted squarefree multiplicative lifting for `indExpSum A`. -/
theorem squarefree_multiplicative_lifting {q : ℕ} (hq : Squarefree q) (A : Finset ℕ) (ω : ℕ → ℕ)
    (hAvoid : ∀ p ∈ q.primeFactors,
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    (∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ))) * (A.card : ℝ) ^ 2 ≤
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖indExpSum A ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
  have h := squarefree_multiplicative_lifting_weighted hq A (fun _ => (1 : ℂ)) ω hAvoid
  have hnorm : ‖∑ _n ∈ A, (1 : ℂ)‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    simp
  rw [hnorm] at h
  refine h.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
  simp [expSum, indExpSum]

/-- **Montgomery's Arithmetic Large Sieve (`Finset.Ico M (M + N)`)**:
for any `A ⊆ Finset.Ico M (M + N)`, level `Q : ℕ`, and `ω : ℕ → ℕ` such that `A` avoids
`ω(p) < p` residue classes modulo every prime `p ≤ Q`,
`|A| * (∑_{1 ≤ q ≤ Q, Squarefree q} ∏_{p ∣ q} ω(p) / (p - ω(p))) ≤ N + 3 Q²`. -/
theorem montgomery_arithmetic_large_sieve_Ico {M N Q : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Ico M (M + N)) (ω : ℕ → ℕ)
    (hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    (A.card : ℝ) * montgomeryL ω Q ≤ (N : ℝ) + 3 * (Q : ℝ) ^ 2 := by
  by_cases hA0 : A.card = 0
  · rw [hA0, Nat.cast_zero, zero_mul]; positivity
  · have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA0)
    have hlow : montgomeryL ω Q * (A.card : ℝ) ^ 2 ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ‖indExpSum A ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
      unfold montgomeryL
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ Q := (Finset.mem_Icc.mp hq).2
      unfold sieveWeight
      by_cases hsqf : Squarefree q
      · rw [if_pos hsqf]
        refine squarefree_multiplicative_lifting hsqf A ω fun p hp => ?_
        have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp_le : p ≤ Q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hsqf.ne_zero)
          (Nat.dvd_of_mem_primeFactors hp)).trans hq_le
        exact hAvoid p hpr hp_le
      · rw [if_neg hsqf, zero_mul]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    let c : ℕ → ℂ := fun n => if n ∈ A then 1 else 0
    have hLS := farey_large_sieve_Ico Q M N c
    have hc_sum : ∀ q a : ℕ,
        ∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) =
          indExpSum A ((a : ℝ) / (q : ℝ)) := by
      intro q a
      unfold indExpSum
      rw [← Finset.sum_subset hA]
      · refine Finset.sum_congr rfl fun n hn => by simp [c, hn]
      · intro n _ hn; simp [c, hn]
    have hc_norm : ∑ n ∈ Finset.Ico M (M + N), ‖c n‖ ^ 2 = (A.card : ℝ) := by
      rw [← Finset.sum_subset hA]
      · calc ∑ n ∈ A, ‖c n‖ ^ 2 = ∑ _n ∈ A, (1 : ℝ) :=
              Finset.sum_congr rfl fun n hn => by simp [c, hn]
          _ = (A.card : ℝ) := by simp
      · intro n _ hn; simp [c, hn]
    simp_rw [hc_sum] at hLS
    rw [hc_norm] at hLS
    have hcomb : montgomeryL ω Q * (A.card : ℝ) ^ 2 ≤ ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * (A.card : ℝ) :=
      hlow.trans hLS
    have hmul : (A.card : ℝ) * montgomeryL ω Q * (A.card : ℝ) ≤ ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * (A.card : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hmul hApos

/-- **Montgomery's Arithmetic Large Sieve (`Finset.Icc (M + 1) (M + N)`)**:
`(|A| : ℝ) * (∑ q ∈ Icc 1 Q, if Squarefree q then ∏ p ∈ q.primeFactors, (ω p : ℝ) / (p - ω p) else 0) ≤ N + 3 * Q²`. -/
theorem montgomery_arithmetic_large_sieve_Icc {M N Q : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc (M + 1) (M + N)) (ω : ℕ → ℕ)
    (hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    (A.card : ℝ) *
        (∑ q ∈ Finset.Icc 1 Q,
          if Squarefree q then ∏ p ∈ q.primeFactors, (ω p : ℝ) / ((p : ℝ) - (ω p : ℝ)) else 0) ≤
      (N : ℝ) + 3 * (Q : ℝ) ^ 2 := by
  have heq : Finset.Icc (M + 1) (M + N) = Finset.Ico (M + 1) ((M + 1) + N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [heq] at hA
  exact montgomery_arithmetic_large_sieve_Ico hA ω hAvoid

/-- `1 ≤ montgomeryL ω Q` whenever `1 ≤ Q` and `ω p < p` for all primes `p ≤ Q`. -/
theorem one_le_montgomeryL {Q : ℕ} (hQ : 1 ≤ Q) (ω : ℕ → ℕ)
    (hω : ∀ p : ℕ, p.Prime → p ≤ Q → ω p < p) :
    1 ≤ montgomeryL ω Q := by
  unfold montgomeryL
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hterm1 : sieveWeight ω 1 = 1 := by simp [sieveWeight]
  rw [← hterm1]
  refine Finset.single_le_sum (fun q hq => ?_) h1
  unfold sieveWeight
  split_ifs with hsqf
  · refine Finset.prod_nonneg fun p hp => ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_le : p ≤ Q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hsqf.ne_zero)
      (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hq).2
    have hlt : (ω p : ℝ) < (p : ℝ) := by exact_mod_cast hω p hpr hp_le
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact le_rfl

/-- Division form of Montgomery's Arithmetic Large Sieve: `|A| ≤ (N + 3 Q²) / L(Q)`. -/
theorem montgomery_arithmetic_large_sieve_div {M N Q : ℕ} (hQ : 1 ≤ Q) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc (M + 1) (M + N)) (ω : ℕ → ℕ)
    (hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω) :
    (A.card : ℝ) ≤ ((N : ℝ) + 3 * (Q : ℝ) ^ 2) / montgomeryL ω Q := by
  have hLpos : 0 < montgomeryL ω Q :=
    lt_of_lt_of_le zero_lt_one (one_le_montgomeryL hQ ω fun p hp hle => (hAvoid p hp hle).1)
  rw [le_div_iff₀ hLpos]
  exact montgomery_arithmetic_large_sieve_Icc hA ω hAvoid

/-! ## Section 2: Elementary Harmonic & Coprime Totient Lower Bounds -/

/-- Elementary harmonic lower bound: `log (Q + 1) ≤ ∑_{m=1}^Q 1 / m` for all `Q : ℕ`. -/
theorem log_add_one_le_harmonic (Q : ℕ) :
    Real.log ((Q : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 Q, (1 : ℝ) / (m : ℝ) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have hIcc : Finset.Icc 1 (Q + 1) = insert (Q + 1) (Finset.Icc 1 Q) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : Q + 1 ∉ Finset.Icc 1 Q := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hpos1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
    have hpos2 : (0 : ℝ) < (Q : ℝ) + 2 := by positivity
    have hstep : Real.log (((Q + 1 : ℕ) : ℝ) + 1) - Real.log ((Q : ℝ) + 1) ≤
        1 / ((Q + 1 : ℕ) : ℝ) := by
      push_cast
      rw [show (Q : ℝ) + 1 + 1 = (Q : ℝ) + 2 by ring]
      rw [← Real.log_div hpos2.ne' hpos1.ne']
      calc Real.log (((Q : ℝ) + 2) / ((Q : ℝ) + 1))
          ≤ ((Q : ℝ) + 2) / ((Q : ℝ) + 1) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
        _ = 1 / ((Q : ℝ) + 1) := by field_simp [hpos1.ne']; ring
    linarith

/-- Elementary harmonic lower bound: `log Q ≤ ∑_{m=1}^Q 1 / m` for `Q ≥ 1`. -/
theorem log_le_harmonic {Q : ℕ} (hQ : 1 ≤ Q) :
    Real.log (Q : ℝ) ≤ ∑ m ∈ Finset.Icc 1 Q, (1 : ℝ) / (m : ℝ) := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  exact (Real.log_le_log hQpos (by linarith)).trans (log_add_one_le_harmonic Q)

/-- For squarefree `n`, `φ(n) = ∏_{p ∈ n.primeFactors} (p - 1)`. -/
theorem totient_eq_prod_sub_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn_ne : n ≠ 0 := hn.ne_zero
    by_cases hn1 : n = 1
    · subst hn1; simp
    · set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hp_dvd : p ∣ n := Nat.minFac_dvd n
      set m : ℕ := n / p
      have hnm : n = p * m := (Nat.mul_div_cancel' hp_dvd).symm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by rw [hm0, mul_zero] at hnm; exact hn_ne hnm
      have hm_lt : m < n := by have := hp.two_le; nlinarith
      have hndvd : ¬ p ∣ m := fun hpm =>
        hp.ne_one (Nat.isUnit_iff.mp (hn p (by obtain ⟨k, hk⟩ := hpm; exact ⟨k, by rw [hnm, hk]; ring⟩)))
      have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hndvd
      have hm_sqf : Squarefree m := hn.squarefree_of_dvd ⟨p, by rw [hnm, mul_comm]⟩
      have hp_not_m : p ∉ m.primeFactors := fun h => hndvd (Nat.dvd_of_mem_primeFactors h)
      have hpf : n.primeFactors = insert p m.primeFactors := by
        ext r
        simp only [Nat.mem_primeFactors, Finset.mem_insert]
        constructor
        · rintro ⟨hr, hrdvd, -⟩
          rw [hnm] at hrdvd
          rcases hr.dvd_mul.mp hrdvd with hrp | hrm
          · left; exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
          · right; exact ⟨hr, hrm, hm_pos.ne'⟩
        · rintro (rfl | ⟨hr, hrm, -⟩)
          · exact ⟨hp, hp_dvd, hn_ne⟩
          · exact ⟨hr, hrm.trans ⟨p, by rw [hnm, mul_comm]⟩, hn_ne⟩
      rw [hpf, Finset.prod_insert hp_not_m, ← ih m hm_lt hm_sqf, hnm,
        Nat.totient_mul hcop, Nat.totient_prime hp]

/-- For squarefree `n`, `sieveWeight (fun _ => 1) n = 1 / φ(n)`. -/
theorem sieveWeight_one_eq_inv_totient {n : ℕ} (hn : Squarefree n) :
    sieveWeight (fun _ => 1) n = (1 : ℝ) / (n.totient : ℝ) := by
  unfold sieveWeight
  rw [if_pos hn, totient_eq_prod_sub_one_of_squarefree hn, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub hp1, Nat.cast_one, one_div]

/-- Squarefree radical `rad(m) = ∏_{p ∈ m.primeFactors} p`. -/
def radical (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

private theorem squarefree_prod_primeFactors (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hp_pr : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs_pr : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hcop : Nat.Coprime p (∏ r ∈ s, r) := by
      refine Nat.Coprime.prod_right fun r hr => ?_
      have hr_pr : r.Prime := hs_pr r hr
      exact (Nat.coprime_primes hp_pr hr_pr).mpr (fun heq => hp (heq ▸ hr))
    exact (Nat.squarefree_mul hcop).mpr ⟨hp_pr.squarefree, ih hs_pr⟩

private theorem radical_squarefree (m : ℕ) : Squarefree (radical m) :=
  squarefree_prod_primeFactors m.primeFactors fun _ hp => Nat.prime_of_mem_primeFactors hp

private theorem radical_primeFactors (m : ℕ) : (radical m).primeFactors = m.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, radical]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    obtain ⟨r, hr, hpr⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hdvd
    have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr_pr).mp hpr
    subst heq
    exact Nat.mem_primeFactors.mp hr
  · rintro ⟨hp, hdvd, hm0⟩
    have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hm0⟩
    exact ⟨hp, Finset.dvd_prod_of_mem _ hmem, (radical_squarefree m).ne_zero⟩

/-- Finite geometric series bound for any prime `p`: `∑_{k=1}^K 1 / p^k ≤ 1 / (p - 1)`. -/
private theorem sum_inv_pow_prime_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((p : ℝ) ^ k)⁻¹ ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsub_pos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
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
  rw [← heq, le_div_iff₀ hsub_pos, mul_comm]
  exact hle

/-- **Harmonic-to-Squarefree-Totient Inequality**:
`∑_{m=1}^Q 1 / m ≤ ∑_{n ≤ Q, Squarefree n} 1 / φ(n)` for every `Q : ℕ`. -/
theorem harmonic_le_sum_squarefree_inv_totient (Q : ℕ) :
    ∑ m ∈ Finset.Icc 1 Q, (1 : ℝ) / (m : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (n.totient : ℝ) := by
  have hmaps : ∀ m ∈ Finset.Icc 1 Q, radical m ∈ (Finset.Icc 1 Q).filter Squarefree := by
    intro m hm
    obtain ⟨hm1, hmQ⟩ := Finset.mem_Icc.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, radical_squarefree m⟩
    · exact Nat.pos_of_ne_zero (radical_squarefree m).ne_zero
    · exact (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)).trans hmQ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn_sqf : Squarefree n := (Finset.mem_filter.mp hn).2
  set F : Finset ℕ := (Finset.Icc 1 Q).filter (fun m => radical m = n)
  let φ : ℕ → (n.primeFactors → ℕ) := fun m p => m.factorization p.1
  let P : Finset (n.primeFactors → ℕ) := Fintype.piFinset fun _ => Finset.Icc 1 Q
  have hφ_maps : ∀ m ∈ F, φ m ∈ P := by
    intro m hm
    obtain ⟨hmI, hrad⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmQ⟩ := Finset.mem_Icc.mp hmI
    refine Fintype.mem_piFinset.mpr fun p => Finset.mem_Icc.mpr ?_
    have hp_mem : p.1 ∈ m.primeFactors := by
      have : n.primeFactors = m.primeFactors := by rw [← hrad, radical_primeFactors]
      exact this ▸ p.2
    have hp_pr : p.1.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpos : 0 < m.factorization p.1 :=
      Nat.Prime.factorization_pos_of_dvd hp_pr (by omega) (Nat.dvd_of_mem_primeFactors hp_mem)
    have hpow : p.1 ^ m.factorization p.1 ∣ m := Nat.ordProj_dvd m p.1
    have hle_pow : m.factorization p.1 ≤ p.1 ^ m.factorization p.1 :=
      le_of_lt (Nat.lt_pow_self hp_pr.one_lt)
    exact ⟨hpos, hle_pow.trans ((Nat.le_of_dvd (by omega) hpow).trans hmQ)⟩
  have hφ_inj : Set.InjOn φ (F : Set ℕ) := by
    intro m₁ hm₁ m₂ hm₂ heq
    obtain ⟨hm₁I, hrad₁⟩ := Finset.mem_filter.mp hm₁
    obtain ⟨hm₂I, hrad₂⟩ := Finset.mem_filter.mp hm₂
    have hm₁_ne : m₁ ≠ 0 := by have := (Finset.mem_Icc.mp hm₁I).1; omega
    have hm₂_ne : m₂ ≠ 0 := by have := (Finset.mem_Icc.mp hm₂I).1; omega
    have hpf₁ : m₁.primeFactors = n.primeFactors := by rw [← hrad₁, radical_primeFactors]
    have hpf₂ : m₂.primeFactors = n.primeFactors := by rw [← hrad₂, radical_primeFactors]
    have hfac₁ : m₁ = ∏ p ∈ n.primeFactors, p ^ m₁.factorization p := by
      rw [← hpf₁]; exact (Nat.prod_factorization_pow_eq_self hm₁_ne).symm
    have hfac₂ : m₂ = ∏ p ∈ n.primeFactors, p ^ m₂.factorization p := by
      rw [← hpf₂]; exact (Nat.prod_factorization_pow_eq_self hm₂_ne).symm
    rw [hfac₁, hfac₂]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := congrFun heq ⟨p, hp⟩
    dsimp only [φ] at this
    rw [this]
  have hterm : ∀ m ∈ F, (1 : ℝ) / (m : ℝ) = ∏ p : n.primeFactors, ((p.1 : ℝ) ^ (φ m p))⁻¹ := by
    intro m hm
    obtain ⟨hmI, hrad⟩ := Finset.mem_filter.mp hm
    have hm_ne : m ≠ 0 := by have := (Finset.mem_Icc.mp hmI).1; omega
    have hpf : m.primeFactors = n.primeFactors := by rw [← hrad, radical_primeFactors]
    have hfac : m = ∏ p ∈ n.primeFactors, p ^ m.factorization p := by
      rw [← hpf]; exact (Nat.prod_factorization_pow_eq_self hm_ne).symm
    conv_lhs => rw [one_div, hfac, Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_attach]
    exact Finset.prod_congr rfl fun p _ => by simp [φ]
  calc ∑ m ∈ F, (1 : ℝ) / (m : ℝ)
      = ∑ m ∈ F, ∏ p : n.primeFactors, ((p.1 : ℝ) ^ (φ m p))⁻¹ :=
        Finset.sum_congr rfl hterm
    _ = ∑ e ∈ F.image φ, ∏ p : n.primeFactors, ((p.1 : ℝ) ^ (e p))⁻¹ :=
        (Finset.sum_image (f := fun e : n.primeFactors → ℕ =>
          ∏ p : n.primeFactors, ((p.1 : ℝ) ^ (e p))⁻¹) hφ_inj).symm
    _ ≤ ∑ e ∈ P, ∏ p : n.primeFactors, ((p.1 : ℝ) ^ (e p))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hφ_maps)
          fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity
    _ = ∏ p : n.primeFactors, ∑ k ∈ Finset.Icc 1 Q, ((p.1 : ℝ) ^ k)⁻¹ := by
        dsimp only [P]
        exact (Finset.prod_univ_sum (t := fun _ : n.primeFactors => Finset.Icc 1 Q)
          (f := fun (p : n.primeFactors) (k : ℕ) => ((p.1 : ℝ) ^ k)⁻¹)).symm
    _ ≤ ∏ p : n.primeFactors, (1 : ℝ) / ((p.1 : ℝ) - 1) := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) fun p _ => ?_
        exact sum_inv_pow_prime_le (Nat.prime_of_mem_primeFactors p.2) Q
    _ = (1 : ℝ) / (n.totient : ℝ) := by
        rw [← sieveWeight_one_eq_inv_totient hn_sqf]
        simp only [sieveWeight, hn_sqf, ↓reduceIte, Nat.cast_one]
        exact Finset.prod_coe_sort n.primeFactors (fun p => (1 : ℝ) / ((p : ℝ) - 1))

/-- Combined logarithmic lower bound: `log (Q + 1) ≤ ∑_{n ≤ Q, Squarefree n} 1 / φ(n)`. -/
theorem log_add_one_le_sum_squarefree_inv_totient (Q : ℕ) :
    Real.log ((Q : ℝ) + 1) ≤
      ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (n.totient : ℝ) :=
  (log_add_one_le_harmonic Q).trans (harmonic_le_sum_squarefree_inv_totient Q)

/-- Combined logarithmic lower bound: `log Q ≤ ∑_{n ≤ Q, Squarefree n} 1 / φ(n)` for `Q ≥ 1`. -/
theorem log_le_sum_squarefree_inv_totient {Q : ℕ} (hQ : 1 ≤ Q) :
    Real.log (Q : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (n.totient : ℝ) :=
  (log_le_harmonic hQ).trans (harmonic_le_sum_squarefree_inv_totient Q)

/-- Squarefree-divisor sum identity for any `q ≥ 1`:
`∑_{d ∣ q, Squarefree d} 1 / φ(d) = q / φ(q)`. -/
theorem sum_divisors_squarefree_inv_totient {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors.filter Squarefree, (1 : ℝ) / (d.totient : ℝ) =
      (q : ℝ) / (q.totient : ℝ) := by
  have hrad_eq : ∑ d ∈ q.divisors.filter Squarefree, (1 : ℝ) / (d.totient : ℝ) =
      ∑ S ∈ q.primeFactors.powerset, ∏ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) := by
    symm
    refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
    · intro S hS
      have hsub : S ⊆ q.primeFactors := Finset.mem_powerset.mp hS
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hq.ne'⟩, ?_⟩
      · exact (Finset.prod_dvd_prod_of_subset S q.primeFactors id hsub).trans
          (Nat.prod_primeFactors_dvd q)
      · exact squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    · intro S₁ hS₁ S₂ hS₂ heq
      have hsub₁ := Finset.mem_powerset.mp hS₁
      have hsub₂ := Finset.mem_powerset.mp hS₂
      have hpf : ∀ S ⊆ q.primeFactors, (∏ p ∈ S, p).primeFactors = S := by
        intro S hsub
        ext r
        simp only [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hr, hdvd, -⟩
          obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
          have hp_pr := Nat.prime_of_mem_primeFactors (hsub hp)
          rwa [(Nat.prime_dvd_prime_iff_eq hr hp_pr).mp hrp]
        · intro hr
          exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr,
            (squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero⟩
      rw [← hpf S₁ hsub₁, ← hpf S₂ hsub₂, heq]
    · intro d hd
      obtain ⟨hd_div, hd_sqf⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdq, -⟩ := Nat.mem_divisors.mp hd_div
      refine ⟨d.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hdq hq.ne'), ?_⟩
      exact Nat.prod_primeFactors_of_squarefree hd_sqf
    · intro S hS
      have hsub := Finset.mem_powerset.mp hS
      have hsqf := squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
      have hpf : (∏ p ∈ S, p).primeFactors = S := by
        ext r
        simp only [Nat.mem_primeFactors]
        constructor
        · rintro ⟨hr, hdvd, -⟩
          obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
          rwa [(Nat.prime_dvd_prime_iff_eq hr (Nat.prime_of_mem_primeFactors (hsub hp))).mp hrp]
        · intro hr
          exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr, hsqf.ne_zero⟩
      rw [← sieveWeight_one_eq_inv_totient hsqf]
      unfold sieveWeight
      rw [if_pos hsqf, hpf]
      refine Finset.prod_congr rfl fun _ _ => by simp
  rw [hrad_eq, ← Finset.prod_one_add]
  have hprod : ∏ p ∈ q.primeFactors, (1 + (1 : ℝ) / ((p : ℝ) - 1)) =
      ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]
    ring
  rw [hprod]
  -- Now compare with `Nat.totient_eq_mul_prod_factors`
  have htot_rat : (q.totient : ℚ) = (q : ℚ) * ∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors q
  have htot_real : (q.totient : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (((p : ℝ) - 1) / (p : ℝ)) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) htot_rat
    push_cast at hcast
    rw [hcast]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp [hp0]
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  rw [eq_div_iff htot_pos.ne', htot_real, mul_left_comm, ← Finset.prod_mul_distrib]
  have hone : ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1) * (((p : ℝ) - 1) / (p : ℝ))) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    field_simp [(by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : (p : ℝ) ≠ 0)]
  rw [hone, mul_one]

/-- **Coprime-to-`q` Sieve-Sum Lower Bound**:
for any `q ≥ 1` and `Q : ℕ`,
`(φ(q) / q) * log (Q + 1) ≤ ∑_{n ≤ Q, Squarefree n, (n, q) = 1} 1 / φ(n)`. -/
theorem coprime_sum_squarefree_inv_totient_ge {q : ℕ} (hq : 0 < q) (Q : ℕ) :
    ((q.totient : ℝ) / (q : ℝ)) * Real.log ((Q : ℝ) + 1) ≤
      ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Squarefree n ∧ Nat.Coprime n q),
        (1 : ℝ) / (n.totient : ℝ) := by
  set D : Finset ℕ := q.divisors.filter Squarefree
  set S : Finset ℕ := (Finset.Icc 1 Q).filter (fun n => Squarefree n ∧ Nat.Coprime n q)
  have hbound : ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (n.totient : ℝ) ≤
      (∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ)) * (∑ m ∈ S, (1 : ℝ) / (m.totient : ℝ)) := by
    rw [Finset.sum_mul_sum]
    let split : ℕ → ℕ × ℕ := fun n => (Nat.gcd n q, n / Nat.gcd n q)
    have hmaps : ∀ n ∈ (Finset.Icc 1 Q).filter Squarefree, split n ∈ D ×ˢ S := by
      intro n hn
      obtain ⟨hnI, hnsqf⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnQ⟩ := Finset.mem_Icc.mp hnI
      set d : ℕ := Nat.gcd n q
      set m : ℕ := n / d
      have hd_dvd_n : d ∣ n := Nat.gcd_dvd_left n q
      have hd_dvd_q : d ∣ q := Nat.gcd_dvd_right n q
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right n hq
      have hnm : n = d * m := (Nat.mul_div_cancel' hd_dvd_n).symm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by rw [hm0, mul_zero] at hnm; omega
      have hm_le : m ≤ Q := (Nat.div_le_self n d).trans hnQ
      have hd_sqf : Squarefree d := hnsqf.squarefree_of_dvd hd_dvd_n
      have hm_sqf : Squarefree m := hnsqf.squarefree_of_dvd ⟨d, by rw [hnm, mul_comm]⟩
      have hm_cop : Nat.Coprime m q := by
        refine Nat.coprime_iff_gcd_eq_one.mpr ?_
        by_contra hne
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
        have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_left m q)
        have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right m q)
        have hpn : p ∣ n := hpm.trans ⟨d, by rw [hnm, mul_comm]⟩
        have hpd : p ∣ d := Nat.dvd_gcd hpn hpq
        have hp2 : p * p ∣ n := by
          obtain ⟨a, ha⟩ := hpd
          obtain ⟨b, hb⟩ := hpm
          exact ⟨a * b, by rw [hnm, ha, hb]; ring⟩
        exact hp.ne_one (Nat.isUnit_iff.mp (hnsqf p hp2))
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd_q, hq.ne'⟩, hd_sqf⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_sqf, hm_cop⟩⟩
    have hinj : Set.InjOn split (((Finset.Icc 1 Q).filter Squarefree : Finset ℕ) : Set ℕ) := by
      intro n₁ _ n₂ _ h
      have h1 : Nat.gcd n₁ q = Nat.gcd n₂ q := congrArg Prod.fst h
      have h2 : n₁ / Nat.gcd n₁ q = n₂ / Nat.gcd n₂ q := congrArg Prod.snd h
      rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ q), ← Nat.mul_div_cancel' (Nat.gcd_dvd_left n₂ q), h2, h1]
    have hval : ∀ n ∈ (Finset.Icc 1 Q).filter Squarefree,
        (1 : ℝ) / (n.totient : ℝ) =
          (1 : ℝ) / ((split n).1.totient : ℝ) * ((1 : ℝ) / ((split n).2.totient : ℝ)) := by
      intro n hn
      set d : ℕ := Nat.gcd n q
      set m : ℕ := n / d
      have hnm : n = d * m := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)).symm
      have hdm_cop : Nat.Coprime d m := by
        have hsm := (Finset.mem_product.mp (hmaps n hn)).2
        have hm_cop : Nat.Coprime m q := (Finset.mem_filter.mp hsm).2.2
        exact (hm_cop.coprime_dvd_right (Nat.gcd_dvd_right n q)).symm
      have htot : n.totient = d.totient * m.totient := by rw [hnm, Nat.totient_mul hdm_cop]
      dsimp only [split, d, m] at htot ⊢
      rw [htot, Nat.cast_mul, one_div, one_div, one_div, mul_inv]
    calc ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (n.totient : ℝ)
        = ∑ n ∈ (Finset.Icc 1 Q).filter Squarefree,
            (1 : ℝ) / ((split n).1.totient : ℝ) * ((1 : ℝ) / ((split n).2.totient : ℝ)) :=
          Finset.sum_congr rfl hval
      _ = ∑ dm ∈ ((Finset.Icc 1 Q).filter Squarefree).image split,
            (1 : ℝ) / (dm.1.totient : ℝ) * ((1 : ℝ) / (dm.2.totient : ℝ)) :=
          (Finset.sum_image (f := fun dm : ℕ × ℕ =>
            (1 : ℝ) / (dm.1.totient : ℝ) * ((1 : ℝ) / (dm.2.totient : ℝ))) hinj).symm
      _ ≤ ∑ dm ∈ D ×ˢ S, (1 : ℝ) / (dm.1.totient : ℝ) * ((1 : ℝ) / (dm.2.totient : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
            fun _ _ _ => by positivity
      _ = ∑ i ∈ D, ∑ j ∈ S, (1 : ℝ) / (i.totient : ℝ) * ((1 : ℝ) / (j.totient : ℝ)) :=
          Finset.sum_product' D S (fun i j => (1 : ℝ) / (i.totient : ℝ) * ((1 : ℝ) / (j.totient : ℝ)))
  rw [sum_divisors_squarefree_inv_totient hq] at hbound
  have hlog := (log_add_one_le_sum_squarefree_inv_totient Q).trans hbound
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hmul := mul_le_mul_of_nonneg_left hlog (div_nonneg hphi_pos.le hq_pos.le)
  refine hmul.trans_eq ?_
  field_simp [hq_pos.ne', hphi_pos.ne']

/-! ## Section 3: Unconditional Brun–Titchmarsh Prime Upper Bounds -/

/-- **Raw Montgomery-Sieve Brun–Titchmarsh Prime Bound** (`Q ≥ 1`):
`π(x + y) - π(x) ≤ (y + 3 Q²) / log (Q + 1) + Q`. -/
theorem brun_titchmarsh_primes_raw (x y Q : ℕ) (hQ : 1 ≤ Q) :
    (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤
      ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) + (Q : ℝ) := by
  set P : Finset ℕ := (Finset.Ioc x (x + y)).filter Nat.Prime
  set A : Finset ℕ := P.filter (fun p => Q < p)
  set B : Finset ℕ := P.filter (fun p => p ≤ Q)
  have hsplit : P.card = A.card + B.card := by
    have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : A ∪ B = P := by
      ext p; simp only [A, B, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hp; by_cases h : Q < p <;> [left; right] <;> exact ⟨hp, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hB_le : B.card ≤ Q := by
    have hsub : B ⊆ Finset.Icc 1 Q := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpr : p.Prime := (Finset.mem_filter.mp hp'.1).2
      exact Finset.mem_Icc.mpr ⟨hpr.pos, hp'.2⟩
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  have hA_sub : A ⊆ Finset.Icc (x + 1) (x + y) := by
    intro p hp
    have hIoc := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hIoc ⊢
    omega
  have hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      1 < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = 1 ∧ ∀ n ∈ A, (n : ZMod p) ∉ Ω := by
    intro p hp hpQ
    refine ⟨hp.one_lt, {0}, Finset.card_singleton 0, fun n hn hmem => ?_⟩
    have h0 : (n : ZMod p) = 0 := Finset.mem_singleton.mp hmem
    have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
    have hn_pr : n.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    have hn_gt : Q < n := (Finset.mem_filter.mp hn).2
    have heq : p = n := (Nat.prime_dvd_prime_iff_eq hp hn_pr).mp hdvd
    omega
  have hMS := montgomery_arithmetic_large_sieve_Icc hA_sub (fun _ => 1) hAvoid
  have hL_ge : Real.log ((Q : ℝ) + 1) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        if Squarefree q then ∏ p ∈ q.primeFactors, ((1 : ℕ) : ℝ) / ((p : ℝ) - ((1 : ℕ) : ℝ)) else 0 := by
    have hsum_eq :
        ∑ q ∈ Finset.Icc 1 Q,
          (if Squarefree q then ∏ p ∈ q.primeFactors, ((1 : ℕ) : ℝ) / ((p : ℝ) - ((1 : ℕ) : ℝ)) else 0) =
        ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, (1 : ℝ) / (q.totient : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hsqf : Squarefree q
      · rw [if_pos hsqf, if_pos hsqf]
        simpa [sieveWeight, hsqf] using sieveWeight_one_eq_inv_totient hsqf
      · rw [if_neg hsqf, if_neg hsqf]
    rw [hsum_eq]
    exact log_add_one_le_sum_squarefree_inv_totient Q
  have hlog_pos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hA_le : (A.card : ℝ) ≤ ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
    rw [le_div_iff₀ hlog_pos]
    exact (mul_le_mul_of_nonneg_left hL_ge (Nat.cast_nonneg _)).trans hMS
  rw [hsplit, Nat.cast_add]
  have hBR : (B.card : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hB_le
  linarith

/-- Raw Montgomery-sieve prime bound using `Real.log Q` for `Q ≥ 2`. -/
theorem brun_titchmarsh_primes_raw_log (x y Q : ℕ) (hQ : 2 ≤ Q) :
    (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤
      ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log (Q : ℝ) + (Q : ℝ) := by
  have hraw := brun_titchmarsh_primes_raw x y Q (by omega)
  have hlog_pos : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hlog_le : Real.log (Q : ℝ) ≤ Real.log ((Q : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdiv : ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
      ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log (Q : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le
  linarith

/-- Elementary odd-prime count bound on `Ioc x (x + y)`: at most `y / 2 + 2` primes. -/
private theorem card_primes_Ioc_le_half_add_two (x y : ℕ) :
    (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤ (y : ℝ) / 2 + 2 := by
  set P : Finset ℕ := (Finset.Ioc x (x + y)).filter Nat.Prime
  set P2 : Finset ℕ := P.filter (fun p => p = 2)
  set Podd : Finset ℕ := P.filter (fun p => p ≠ 2)
  have hsplit : P.card = P2.card + Podd.card := by
    have hdisj : Disjoint P2 Podd := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : P2 ∪ Podd = P := by
      ext p; simp only [P2, Podd, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hP2 : P2.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
    rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
  have hPodd : Podd.card ≤ y / 2 + 1 := by
    have hsub : Podd.image (fun p => (p - (x + 1)) / 2) ⊆ Finset.range (y / 2 + 1) := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      have hIoc := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      simp only [Finset.mem_Ioc] at hIoc
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
    have hinj : Set.InjOn (fun p => (p - (x + 1)) / 2) (Podd : Set ℕ) := by
      intro p₁ hp₁ p₂ hp₂ heq
      have hI1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1
      have hI2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).1
      have hpr1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).2
      have hpr2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).2
      have hne1 : p₁ ≠ 2 := (Finset.mem_filter.mp hp₁).2
      have hne2 : p₂ ≠ 2 := (Finset.mem_filter.mp hp₂).2
      have hodd1 : p₁ % 2 = 1 := (hpr1.eq_two_or_odd).resolve_left hne1
      have hodd2 : p₂ % 2 = 1 := (hpr2.eq_two_or_odd).resolve_left hne2
      dsimp only at heq
      simp only [Finset.mem_Ioc] at hI1 hI2
      omega
    have hcard := (Finset.card_image_of_injOn hinj).symm.trans_le
      ((Finset.card_le_card hsub).trans_eq (Finset.card_range _))
    exact hcard
  have hdiv : ((y / 2 : ℕ) : ℝ) ≤ (y : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self y 2
  rw [hsplit, Nat.cast_add]
  have h1 : (P2.card : ℝ) ≤ 1 := by exact_mod_cast hP2
  have h2 : (Podd.card : ℝ) ≤ ((y / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hPodd
  linarith

/-- **Unconditional Brun–Titchmarsh Prime Upper Bound (Explicit Form)**:
for all `x, y : ℕ` with `9 ≤ y`,
`π(x + y) - π(x) ≤ 5 * y / log y`. -/
theorem brun_titchmarsh_primes (x y : ℕ) (hy : 9 ≤ y) :
    (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤ 5 * (y : ℝ) / Real.log (y : ℝ) := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hlog_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hl2_lo : (693 : ℝ) / 1000 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2_hi : Real.log 2 < (694 : ℝ) / 1000 := by linarith [Real.log_two_lt_d9]
  by_cases hy128 : y ≤ 128
  · have hlog_le : Real.log (y : ℝ) ≤ 5 := by
      have h1 : Real.log (y : ℝ) ≤ Real.log ((2 : ℝ) ^ (7 : ℕ)) :=
        Real.log_le_log hy_pos (by exact_mod_cast (by omega : y ≤ 2 ^ 7))
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hcard : (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; omega)
    rw [le_div_iff₀ hlog_pos]
    nlinarith
  · by_cases hy4096 : y ≤ 4096
    · have hlog_le : Real.log (y : ℝ) ≤ (833 : ℝ) / 100 := by
        have h1 : Real.log (y : ℝ) ≤ Real.log ((2 : ℝ) ^ (12 : ℕ)) :=
          Real.log_le_log hy_pos (by exact_mod_cast (by omega : y ≤ 2 ^ 12))
        rw [Real.log_pow] at h1
        push_cast at h1
        linarith
      have hcard := card_primes_Ioc_le_half_add_two x y
      have hy_ge : (129 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 129 ≤ y)
      rw [le_div_iff₀ hlog_pos]
      nlinarith
    · -- Main regime `y > 4096`: apply Montgomery's sieve with `Q = ⌊√(y / 3)⌋₊`.
      have hy_gt : (4096 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 4096 < y)
      have hlog_ge : (831 : ℝ) / 100 < Real.log (y : ℝ) := by
        have h1 : Real.log ((2 : ℝ) ^ (12 : ℕ)) < Real.log (y : ℝ) :=
          Real.log_lt_log (by positivity) (by norm_num; linarith)
        rw [Real.log_pow] at h1
        push_cast at h1
        linarith
      set Q : ℕ := ⌊Real.sqrt ((y : ℝ) / 3)⌋₊
      have hsq_pos : 0 < Real.sqrt ((y : ℝ) / 3) := Real.sqrt_pos.mpr (by positivity)
      have hQ_ge1 : 1 ≤ Q := Nat.le_floor (Real.le_sqrt_of_sq_le (by linarith))
      have hQ_le : (Q : ℝ) ≤ Real.sqrt ((y : ℝ) / 3) := Nat.floor_le hsq_pos.le
      have hQ_gt : Real.sqrt ((y : ℝ) / 3) < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
      have h3Q2 : 3 * (Q : ℝ) ^ 2 ≤ (y : ℝ) := by
        have hsq : (Q : ℝ) ^ 2 ≤ (y : ℝ) / 3 := by
          calc (Q : ℝ) ^ 2 ≤ (Real.sqrt ((y : ℝ) / 3)) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
            _ = (y : ℝ) / 3 := Real.sq_sqrt (by positivity)
        linarith
      have hlog3_le : Real.log 3 ≤ (139 : ℝ) / 100 := by
        have h1 : Real.log (3 : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) :=
          Real.log_le_log (by norm_num) (by norm_num)
        rw [Real.log_pow] at h1
        push_cast at h1
        linarith
      have hlogQ1 : (415 : ℝ) / 1000 * Real.log (y : ℝ) ≤ Real.log ((Q : ℝ) + 1) := by
        have h1 : Real.log (Real.sqrt ((y : ℝ) / 3)) ≤ Real.log ((Q : ℝ) + 1) :=
          Real.log_le_log hsq_pos hQ_gt.le
        rw [Real.log_sqrt (by positivity), Real.log_div hy_pos.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h1
        linarith
      have hlogQ1_pos : 0 < Real.log ((Q : ℝ) + 1) := by linarith
      have hraw := brun_titchmarsh_primes_raw x y Q hQ_ge1
      have hterm1 : ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
          (482 : ℝ) / 100 * (y : ℝ) / Real.log (y : ℝ) := by
        rw [div_le_div_iff₀ hlogQ1_pos hlog_pos]
        nlinarith
      have hterm2 : (Q : ℝ) ≤ (18 : ℝ) / 100 * (y : ℝ) / Real.log (y : ℝ) := by
        rw [le_div_iff₀ hlog_pos]
        -- Bound `log y` linearly in `√y`: `log(y / 4096) = 2 log(√y / 64) ≤ 2(√y / 64 - 1)`
        have hsy_gt : (64 : ℝ) < Real.sqrt (y : ℝ) := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 64)]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num; linarith)
        have hlog_lin : Real.log (y : ℝ) ≤ (833 : ℝ) / 100 + Real.sqrt (y : ℝ) / 32 := by
          have hdiv_pos : (0 : ℝ) < Real.sqrt (y : ℝ) / 64 := by positivity
          have hstep := Real.log_le_sub_one_of_pos hdiv_pos
          have hlog4096 : Real.log (4096 : ℝ) ≤ (833 : ℝ) / 100 := by
            have : (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) := by norm_num
            rw [this, Real.log_pow]; push_cast; linarith
          have heq : Real.log (y : ℝ) = Real.log (4096 : ℝ) + 2 * Real.log (Real.sqrt (y : ℝ) / 64) := by
            rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hy_pos.le]
            have : Real.log (4096 : ℝ) = 2 * Real.log (64 : ℝ) := by
              rw [show (4096 : ℝ) = (64 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
            linarith
          linarith
        have hQ_sy : (Q : ℝ) ≤ Real.sqrt (y : ℝ) := by
          refine hQ_le.trans (Real.sqrt_le_sqrt (by linarith))
        have hsy_sq : Real.sqrt (y : ℝ) * Real.sqrt (y : ℝ) = (y : ℝ) := Real.mul_self_sqrt hy_pos.le
        have hsy_le : Real.sqrt (y : ℝ) ≤ (y : ℝ) / 64 := by nlinarith
        nlinarith [Nat.cast_nonneg (α := ℝ) Q]
      have hadd_eq : (482 : ℝ) / 100 * (y : ℝ) / Real.log (y : ℝ) +
          (18 : ℝ) / 100 * (y : ℝ) / Real.log (y : ℝ) = 5 * (y : ℝ) / Real.log (y : ℝ) := by ring
      linarith

/-- Elementary upper bound `log (a * u) ≤ δ * u` for sufficiently large `u`. -/
private theorem log_mul_le_linear {a δ u : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hu : 0 < u)
    (hlarge : (2 / δ) * max 0 (Real.log (2 * a / δ)) ≤ u) :
    Real.log (a * u) ≤ δ * u := by
  set C : ℝ := 2 * a / δ
  have hC : 0 < C := by positivity
  have hsplit : Real.log (a * u) = Real.log C + Real.log (a * u / C) := by
    rw [Real.log_div (by positivity) hC.ne']; ring
  have hstep := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hu) hC)
  have hratio : a * u / C = (δ / 2) * u := by
    dsimp only [C]; field_simp [ha.ne', hδ.ne']
  have hC_le : Real.log C ≤ (δ / 2) * u := by
    have h1 : Real.log C ≤ max 0 (Real.log C) := le_max_right _ _
    have h2 : (δ / 2) * ((2 / δ) * max 0 (Real.log C)) ≤ (δ / 2) * u :=
      mul_le_mul_of_nonneg_left hlarge (by positivity)
    have h3 : (δ / 2) * ((2 / δ) * max 0 (Real.log C)) = max 0 (Real.log C) := by
      field_simp [hδ.ne']
    linarith
  linarith

/-- **Sharp Asymptotic Brun–Titchmarsh Prime Upper Bound (`(2 + ε) y / log y`)**:
for every `ε > 0`, there exists `Y₀ : ℕ` such that for all `x : ℕ` and `y ≥ Y₀`,
`π(x + y) - π(x) ≤ (2 + ε) * y / log y`. -/
theorem brun_titchmarsh_primes_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₀ : ℕ, ∀ x y : ℕ, Y₀ ≤ y →
      (((Finset.Ioc x (x + y)).filter Nat.Prime).card : ℝ) ≤
        (2 + ε) * (y : ℝ) / Real.log (y : ℝ) := by
  set δ : ℝ := min (1 / 4) (ε / 10)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le_quarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδ_le_eps : δ ≤ ε / 10 := min_le_right _ _
  set L₀ : ℝ := max (max 4 (1 / δ)) ((2 / δ) * max 0 (Real.log (6 / δ)))
  set Y₁ : ℝ := max (Real.exp L₀) ((2 / (3 * δ ^ 2)) * max 0 (Real.log (2 / (3 * δ ^ 2))))
  refine ⟨max 16 ⌈Y₁⌉₊, fun x y hy => ?_⟩
  have hy16 : 16 ≤ y := le_trans (le_max_left _ _) hy
  have hyY₁ : Y₁ ≤ (y : ℝ) := (Nat.le_ceil Y₁).trans (by exact_mod_cast le_trans (le_max_right 16 _) hy)
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hL_ge : L₀ ≤ Real.log (y : ℝ) := by
    have hexp : Real.exp L₀ ≤ (y : ℝ) := (le_max_left _ _).trans hyY₁
    have h := Real.log_le_log (Real.exp_pos L₀) hexp
    rwa [Real.log_exp] at h
  have hlog_ge4 : 4 ≤ Real.log (y : ℝ) := ((le_max_left 4 _).trans (le_max_left _ _)).trans hL_ge
  have hlog_pos : 0 < Real.log (y : ℝ) := by linarith
  have hlog_inv : 1 / Real.log (y : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlog_pos]
    have h1 : 1 / δ ≤ Real.log (y : ℝ) := ((le_max_right 4 _).trans (le_max_left _ _)).trans hL_ge
    have := mul_le_mul_of_nonneg_left h1 hδ_pos.le
    rwa [mul_one_div_cancel hδ_pos.ne'] at this
  have hlog_3log : Real.log (3 * Real.log (y : ℝ)) ≤ δ * Real.log (y : ℝ) := by
    refine log_mul_le_linear (a := 3) (by norm_num) hδ_pos hlog_pos ?_
    have h6 : 2 * (3 : ℝ) / δ = 6 / δ := by ring
    rw [h6]
    exact (le_max_right _ _).trans hL_ge
  have hlog_le_3d2y : Real.log (y : ℝ) ≤ 3 * δ ^ 2 * (y : ℝ) := by
    have h := log_mul_le_linear (a := 1) (δ := 3 * δ ^ 2) zero_lt_one (by positivity) hy_pos (by
      have h2 : 2 * (1 : ℝ) / (3 * δ ^ 2) = 2 / (3 * δ ^ 2) := by ring
      rw [h2]
      exact (le_max_right _ _).trans hyY₁)
    simpa using h
  set R : ℝ := Real.sqrt ((y : ℝ) / (3 * Real.log (y : ℝ)))
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  set Q : ℕ := ⌊R⌋₊
  have hQ_ge1 : 1 ≤ Q := by
    refine Nat.le_floor (Real.le_sqrt_of_sq_le ?_)
    rw [Nat.cast_one, one_pow, le_div_iff₀ (by positivity)]
    have : 9 * δ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hQ_le : (Q : ℝ) ≤ R := Nat.floor_le hR_pos.le
  have hQ_gt : R < (Q : ℝ) + 1 := Nat.lt_floor_add_one R
  have h3Q2 : 3 * (Q : ℝ) ^ 2 ≤ δ * (y : ℝ) := by
    have h1 : (Q : ℝ) ^ 2 ≤ (y : ℝ) / (3 * Real.log (y : ℝ)) := by
      calc (Q : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
        _ = (y : ℝ) / (3 * Real.log (y : ℝ)) := Real.sq_sqrt (by positivity)
    have h2 : 3 * (Q : ℝ) ^ 2 ≤ (y : ℝ) / Real.log (y : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
      refine hmul.trans_eq ?_
      field_simp [hlog_pos.ne']
    calc 3 * (Q : ℝ) ^ 2 ≤ (y : ℝ) * (1 / Real.log (y : ℝ)) := by rwa [mul_one_div]
      _ ≤ (y : ℝ) * δ := mul_le_mul_of_nonneg_left hlog_inv hy_pos.le
      _ = δ * (y : ℝ) := mul_comm _ _
  have hlogQ1 : (1 - δ) / 2 * Real.log (y : ℝ) ≤ Real.log ((Q : ℝ) + 1) := by
    have h1 : Real.log R ≤ Real.log ((Q : ℝ) + 1) := Real.log_le_log hR_pos hQ_gt.le
    rw [show Real.log R = (Real.log (y : ℝ) - Real.log (3 * Real.log (y : ℝ))) / 2 by
      dsimp only [R]
      rw [Real.log_sqrt (by positivity), Real.log_div hy_pos.ne' (by positivity)]] at h1
    linarith
  have hlogQ1_pos : 0 < Real.log ((Q : ℝ) + 1) := by nlinarith
  have hraw := brun_titchmarsh_primes_raw x y Q hQ_ge1
  have hterm1 : ((y : ℝ) + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
      (2 * (1 + δ) / (1 - δ)) * (y : ℝ) / Real.log (y : ℝ) := by
    have h1d : 0 < 1 - δ := by linarith
    rw [div_le_div_iff₀ hlogQ1_pos hlog_pos]
    have hnum : (y : ℝ) + 3 * (Q : ℝ) ^ 2 ≤ (1 + δ) * (y : ℝ) := by linarith
    have hlhs : ((y : ℝ) + 3 * (Q : ℝ) ^ 2) * Real.log (y : ℝ) ≤
        (1 + δ) * (y : ℝ) * Real.log (y : ℝ) :=
      mul_le_mul_of_nonneg_right hnum hlog_pos.le
    have hrhs : (1 + δ) * (y : ℝ) * Real.log (y : ℝ) ≤
        (2 * (1 + δ) / (1 - δ)) * (y : ℝ) * Real.log ((Q : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hlogQ1 (by positivity : 0 ≤ (2 * (1 + δ) / (1 - δ)) * (y : ℝ))
      refine le_trans ?_ hmul
      have : (2 * (1 + δ) / (1 - δ)) * (y : ℝ) * ((1 - δ) / 2 * Real.log (y : ℝ)) =
          (1 + δ) * (y : ℝ) * Real.log (y : ℝ) := by
        field_simp [h1d.ne']
      linarith
    exact hlhs.trans hrhs
  have hterm2 : (Q : ℝ) ≤ δ * (y : ℝ) / Real.log (y : ℝ) := by
    rw [le_div_iff₀ hlog_pos]
    have hsq : ((Q : ℝ) * Real.log (y : ℝ)) ^ 2 ≤ (δ * (y : ℝ)) ^ 2 := by
      have hq2 : (Q : ℝ) ^ 2 ≤ (y : ℝ) / (3 * Real.log (y : ℝ)) := by
        calc (Q : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
          _ = (y : ℝ) / (3 * Real.log (y : ℝ)) := Real.sq_sqrt (by positivity)
      calc ((Q : ℝ) * Real.log (y : ℝ)) ^ 2
          = (Q : ℝ) ^ 2 * (Real.log (y : ℝ)) ^ 2 := mul_pow _ _ 2
        _ ≤ ((y : ℝ) / (3 * Real.log (y : ℝ))) * (Real.log (y : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
        _ = (y : ℝ) * Real.log (y : ℝ) / 3 := by field_simp [hlog_pos.ne']
        _ ≤ (y : ℝ) * (3 * δ ^ 2 * (y : ℝ)) / 3 := by
            gcongr
        _ = (δ * (y : ℝ)) ^ 2 := by ring
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) Q) hlog_pos.le, mul_nonneg hδ_pos.le hy_pos.le]
  have hconst : 2 * (1 + δ) / (1 - δ) + δ ≤ 2 + ε := by
    have h1d : (3 : ℝ) / 4 ≤ 1 - δ := by linarith
    have h1 : 2 * (1 + δ) / (1 - δ) = 2 + 4 * δ / (1 - δ) := by
      field_simp [(by linarith : 1 - δ ≠ 0)]; ring
    have h2 : 4 * δ / (1 - δ) ≤ 16 / 3 * δ := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - δ)]
      nlinarith
    linarith
  have hcomb : (2 * (1 + δ) / (1 - δ)) * (y : ℝ) / Real.log (y : ℝ) +
      δ * (y : ℝ) / Real.log (y : ℝ) ≤ (2 + ε) * (y : ℝ) / Real.log (y : ℝ) := by
    rw [← add_div, ← add_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hy_pos.le) hlog_pos.le
  linarith

/-- **Raw Montgomery-Sieve Brun–Titchmarsh Bound in Arithmetic Progressions**:
for `q ≥ 1`, `Nat.Coprime a q`, and any `x, y, Q : ℕ` with `1 ≤ Q`,
`π(x + y; q, a) - π(x; q, a) ≤ (q / φ(q)) * (y / q + 1 + 3 Q²) / log (Q + 1) + Q / q + 1`. -/
theorem brun_titchmarsh_ap_raw {q a : ℕ} (hq : 0 < q) (_hcop : Nat.Coprime a q)
    (x y Q : ℕ) (hQ : 1 ≤ Q) :
    (((Finset.Ioc x (x + y)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) ≤
      ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) +
        (((Q / q : ℕ) : ℝ) + 1) := by
  set P : Finset ℕ := (Finset.Ioc x (x + y)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  set P_hi : Finset ℕ := P.filter (fun p => Q < p)
  set P_lo : Finset ℕ := P.filter (fun p => p ≤ Q)
  have hsplit : P.card = P_hi.card + P_lo.card := by
    have hdisj : Disjoint P_hi P_lo := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : P_hi ∪ P_lo = P := by
      ext p; simp only [P_hi, P_lo, Finset.mem_union, Finset.mem_filter]; constructor
      · rintro (h | h) <;> exact h.1
      · intro hp; by_cases h : Q < p <;> [left; right] <;> exact ⟨hp, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- Bound small primes `p ≤ Q` with `p ≡ a [MOD q]`
  have hPlo_le : P_lo.card ≤ Q / q + 1 := by
    have hsub : P_lo.image (fun p => p / q) ⊆ Finset.range (Q / q + 1) := by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      have hpQ : p ≤ Q := (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hpQ))
    have hinj : Set.InjOn (fun p => p / q) (P_lo : Set ℕ) := by
      intro p₁ hp₁ p₂ hp₂ heq
      dsimp only at heq
      have hm1 : p₁ ≡ a [MOD q] := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).2.2
      have hm2 : p₂ ≡ a [MOD q] := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).2.2
      have hmod : p₁ % q = p₂ % q := hm1.trans hm2.symm
      rw [← Nat.div_add_mod p₁ q, ← Nat.div_add_mod p₂ q, heq, hmod]
    exact (Finset.card_image_of_injOn hinj).symm.trans_le
      ((Finset.card_le_card hsub).trans_eq (Finset.card_range _))
  -- Parameterize `P_hi` via `x₀ + k * q` with `k ∈ Ico 0 (y / q + 1)`
  set r : ℕ := (a % q + q - (x + 1) % q) % q
  have hr_lt : r < q := Nat.mod_lt _ hq
  set x₀ : ℕ := x + 1 + r
  have hx₀_mod : x₀ ≡ a [MOD q] := by
    show x₀ % q = a % q
    have hx1 : (x + 1) % q < q := Nat.mod_lt _ hq
    have ha1 : a % q < q := Nat.mod_lt _ hq
    dsimp only [x₀, r]
    rw [Nat.add_mod, Nat.mod_mod]
    have hstep : ((x + 1) % q + (a % q + q - (x + 1) % q) % q) % q =
        ((x + 1) % q + (a % q + q - (x + 1) % q)) % q :=
      Nat.add_mod_mod _ _ _
    rw [hstep]
    have hsum : (x + 1) % q + (a % q + q - (x + 1) % q) = a % q + q := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ha1]
  set A : Finset ℕ := (Finset.Ico 0 (y / q + 1)).filter
    (fun k => x₀ + k * q ≤ x + y ∧ (x₀ + k * q).Prime ∧ Q < x₀ + k * q)
  have hcard_eq : P_hi.card = A.card := by
    symm
    refine Finset.card_bij (fun k _ => x₀ + k * q) ?_ ?_ ?_
    · intro k hk
      obtain ⟨-, hle, hpr, hgt⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hle⟩, hpr, ?_⟩, hgt⟩
      show (x₀ + k * q) % q = a % q
      rw [Nat.add_mul_mod_self_right]
      exact hx₀_mod
    · intro k₁ _ k₂ _ heq
      have : k₁ * q = k₂ * q := by omega
      exact Nat.eq_of_mul_eq_mul_right hq this
    · intro p hp
      obtain ⟨hpP, hpQ⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpI, hpPr, hpMod⟩ := Finset.mem_filter.mp hpP
      obtain ⟨hxp, hpxy⟩ := Finset.mem_Ioc.mp hpI
      have hx₀_le : x₀ ≤ p := by
        by_contra hlt
        push Not at hlt
        have hdvd : q ∣ x₀ - p := by
          have : x₀ % q = p % q := hx₀_mod.trans hpMod.symm
          exact (Nat.modEq_iff_dvd' (by omega)).mp this.symm
        have hpos : 0 < x₀ - p := by omega
        have hge : q ≤ x₀ - p := Nat.le_of_dvd hpos hdvd
        omega
      have hdvd : q ∣ p - x₀ := by
        have : p % q = x₀ % q := hpMod.trans hx₀_mod.symm
        exact (Nat.modEq_iff_dvd' hx₀_le).mp this.symm
      set k : ℕ := (p - x₀) / q
      have hkq : x₀ + k * q = p := by
        have h1 : k * q = p - x₀ := by rw [mul_comm]; exact Nat.mul_div_cancel' hdvd
        omega
      have hk_lt : k < y / q + 1 := by
        have hk_le : k * q ≤ y := by omega
        have : k ≤ y / q := (Nat.le_div_iff_mul_le hq).mpr hk_le
        omega
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.zero_le _, hk_lt⟩,
        by omega, hkq.symm ▸ hpPr, hkq.symm ▸ hpQ⟩, hkq⟩
  -- Sieve `A` with `ω(p) = if ¬ p ∣ q then 1 else 0`
  let ω : ℕ → ℕ := fun p => if ¬ p ∣ q then 1 else 0
  have hAvoid : ∀ p : ℕ, p.Prime → p ≤ Q →
      ω p < p ∧ ∃ Ω : Finset (ZMod p), Ω.card = ω p ∧ ∀ k ∈ A, (k : ZMod p) ∉ Ω := by
    intro p hp hpQ
    have : NeZero p := ⟨hp.ne_zero⟩
    by_cases hpd : p ∣ q
    · refine ⟨by simp [ω, hpd, hp.pos], ∅, by simp [ω, hpd], fun _ _ h => absurd h (Finset.notMem_empty _)⟩
    · have hcop_pq : Nat.Coprime q p := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hu : IsUnit (q : ZMod p) := (ZMod.isUnit_iff_coprime q p).mpr hcop_pq
      let r₀ : ZMod p := -(x₀ : ZMod p) * (hu.unit⁻¹ : (ZMod p)ˣ)
      refine ⟨by simp [ω, hpd, hp.one_lt], {r₀}, by simp [ω, hpd], fun k hk hmem => ?_⟩
      have hkr : (k : ZMod p) = r₀ := Finset.mem_singleton.mp hmem
      have hzero : ((x₀ + k * q : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [hkr]
        dsimp only [r₀]
        rw [mul_assoc, show ((hu.unit⁻¹ : (ZMod p)ˣ) : ZMod p) * (q : ZMod p) = 1 by
          simp, mul_one, add_neg_cancel]
      have hdvd : p ∣ x₀ + k * q := (ZMod.natCast_eq_zero_iff _ p).mp hzero
      obtain ⟨-, -, hpr, hgt⟩ := Finset.mem_filter.mp hk
      have heq : p = x₀ + k * q := (Nat.prime_dvd_prime_iff_eq hp hpr).mp hdvd
      omega
  have hA_sub : A ⊆ Finset.Ico 0 (0 + (y / q + 1)) := by
    rw [zero_add]
    exact Finset.filter_subset _ _
  have hMS := montgomery_arithmetic_large_sieve_Ico (M := 0) (N := y / q + 1) (Q := Q) hA_sub ω hAvoid
  have hL_eq : montgomeryL ω Q =
      ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Squarefree n ∧ Nat.Coprime n q),
        (1 : ℝ) / (n.totient : ℝ) := by
    unfold montgomeryL
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    unfold sieveWeight
    by_cases hsqf : Squarefree n
    · rw [if_pos hsqf]
      by_cases hcop_nq : Nat.Coprime n q
      · rw [if_pos ⟨hsqf, hcop_nq⟩, ← sieveWeight_one_eq_inv_totient hsqf]
        unfold sieveWeight
        rw [if_pos hsqf]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hndvd : ¬ p ∣ q := fun hpd =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.dvd_one.mp (hcop_nq.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpd))
        simp [ω, hndvd]
      · rw [if_neg (fun h => hcop_nq h.2)]
        have hne : Nat.gcd n q ≠ 1 := fun h1 => hcop_nq (Nat.coprime_iff_gcd_eq_one.mpr h1)
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
        have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n q)
        have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right n q)
        have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hsqf.ne_zero⟩
        refine Finset.prod_eq_zero hp_mem ?_
        simp [ω, hpq]
    · rw [if_neg hsqf, if_neg (fun h => hsqf h.1)]
  have hL_ge : ((q.totient : ℝ) / (q : ℝ)) * Real.log ((Q : ℝ) + 1) ≤ montgomeryL ω Q := by
    rw [hL_eq]
    exact coprime_sum_squarefree_inv_totient_ge hq Q
  have hlog_pos : 0 < Real.log ((Q : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hden_pos : 0 < ((q.totient : ℝ) / (q : ℝ)) * Real.log ((Q : ℝ) + 1) := by positivity
  have hA_le : (A.card : ℝ) ≤
      ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) := by
    have h1 : (A.card : ℝ) * (((q.totient : ℝ) / (q : ℝ)) * Real.log ((Q : ℝ) + 1)) ≤
        (((y / q + 1 : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) :=
      (mul_le_mul_of_nonneg_left hL_ge (Nat.cast_nonneg _)).trans hMS
    have h2 : (A.card : ℝ) ≤
        ((((y / q + 1 : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2)) / (((q.totient : ℝ) / (q : ℝ)) * Real.log ((Q : ℝ) + 1)) :=
      (le_div_iff₀ hden_pos).mpr h1
    refine h2.trans_eq ?_
    push_cast
    field_simp [hq_pos.ne', hphi_pos.ne', hlog_pos.ne']
  rw [hsplit, hcard_eq, Nat.cast_add]
  have hPloR : (P_lo.card : ℝ) ≤ ((Q / q : ℕ) : ℝ) + 1 := by exact_mod_cast hPlo_le
  linarith

/-- **Unconditional Brun–Titchmarsh Prime Upper Bound in Arithmetic Progressions**:
for `q ≥ 1`, `Nat.Coprime a q`, and `y ≥ 9 * q`,
`π(x + y; q, a) - π(x; q, a) ≤ 10 * y / (φ(q) * log (y / q))`. -/
theorem brun_titchmarsh_ap {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    (x y : ℕ) (hy : 9 * q ≤ y) :
    (((Finset.Ioc x (x + y)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) ≤
      10 * (y : ℝ) / ((q.totient : ℝ) * Real.log ((y : ℝ) / (q : ℝ))) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hphi_le : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  set u : ℝ := (y : ℝ) / (q : ℝ)
  have hu_ge9 : 9 ≤ u := (le_div_iff₀ hq_pos).mpr (by exact_mod_cast hy)
  have hu_pos : 0 < u := by linarith
  have hlogu_pos : 0 < Real.log u := Real.log_pos (by linarith)
  set Q : ℕ := ⌊Real.sqrt (u / 3)⌋₊
  have hsq_pos : 0 < Real.sqrt (u / 3) := Real.sqrt_pos.mpr (by positivity)
  have hQ_ge1 : 1 ≤ Q := Nat.le_floor (Real.le_sqrt_of_sq_le (by linarith))
  have hQ_le : (Q : ℝ) ≤ Real.sqrt (u / 3) := Nat.floor_le hsq_pos.le
  have hQ_gt : Real.sqrt (u / 3) < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3Q2 : 3 * (Q : ℝ) ^ 2 ≤ u := by
    have hsq : (Q : ℝ) ^ 2 ≤ u / 3 := by
      calc (Q : ℝ) ^ 2 ≤ (Real.sqrt (u / 3)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
        _ = u / 3 := Real.sq_sqrt (by positivity)
    linarith
  have hdiv_le : ((y / q : ℕ) : ℝ) ≤ u :=
    (le_div_iff₀ hq_pos).mpr (by exact_mod_cast Nat.div_mul_le_self y q)
  have hlogQ1 : (1 / 4 : ℝ) * Real.log u ≤ Real.log ((Q : ℝ) + 1) := by
    have h1 : Real.log (Real.sqrt (u / 3)) ≤ Real.log ((Q : ℝ) + 1) :=
      Real.log_le_log hsq_pos hQ_gt.le
    rw [Real.log_sqrt (by positivity)] at h1
    have h2 : u ≤ (u / 3) ^ 2 := by nlinarith
    have h3 : Real.log u ≤ 2 * Real.log (u / 3) := by
      have := Real.log_le_log hu_pos h2
      rwa [Real.log_pow] at this
    linarith
  have hlogQ1_pos : 0 < Real.log ((Q : ℝ) + 1) := by linarith
  have hraw := brun_titchmarsh_ap_raw hq hcop x y Q hQ_ge1
  have hterm1 :
      ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
        (76 / 9 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have hnum : ((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2 ≤ (19 / 9 : ℝ) * u := by linarith
    have hstep1 : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) ≤
        (19 / 9 : ℝ) * (y : ℝ) / (q.totient : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hnum (div_nonneg hq_pos.le hphi_pos.le)
      refine hmul.trans_eq ?_
      dsimp only [u]; field_simp [hq_pos.ne', hphi_pos.ne']
    rw [div_le_div_iff₀ hlogQ1_pos (mul_pos hphi_pos hlogu_pos)]
    have hstep2 : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) * (q.totient : ℝ) ≤
        (19 / 9 : ℝ) * (y : ℝ) := by
      have := mul_le_mul_of_nonneg_right hstep1 hphi_pos.le
      rwa [div_mul_cancel₀ _ hphi_pos.ne'] at this
    have hstep3 : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) *
        ((q.totient : ℝ) * Real.log u) ≤ (19 / 9 : ℝ) * (y : ℝ) * Real.log u := by
      calc _ = (((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) * (q.totient : ℝ)) * Real.log u := by ring
        _ ≤ (19 / 9 : ℝ) * (y : ℝ) * Real.log u := mul_le_mul_of_nonneg_right hstep2 hlogu_pos.le
    have hy_nn : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hQdiv_le : ((Q / q : ℕ) : ℝ) ≤ (Q : ℝ) / (q : ℝ) :=
    (le_div_iff₀ hq_pos).mpr (by exact_mod_cast Nat.div_mul_le_self Q q)
  have hlogu_sqrt : Real.log u ≤ 2 * Real.sqrt u := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu_pos)
    rw [Real.log_sqrt hu_pos.le] at h
    linarith
  have hterm2 : ((Q / q : ℕ) : ℝ) ≤ (6 / 5 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have h1 : (Q : ℝ) * Real.log u ≤ (6 / 5 : ℝ) * u := by
      have hsq : (Real.sqrt (u / 3) * (2 * Real.sqrt u)) ^ 2 ≤ ((6 / 5 : ℝ) * u) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hu_pos.le]
        nlinarith
      have hprod : Real.sqrt (u / 3) * (2 * Real.sqrt u) ≤ (6 / 5 : ℝ) * u := by
        nlinarith [Real.sqrt_nonneg (u / 3), Real.sqrt_nonneg u]
      exact (mul_le_mul hQ_le hlogu_sqrt hlogu_pos.le hsq_pos.le).trans hprod
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hu_le_y : u ≤ (y : ℝ) := by
      dsimp only [u]; exact div_le_self (Nat.cast_nonneg _) hq_ge1
    refine hQdiv_le.trans ?_
    rw [div_le_div_iff₀ hq_pos (mul_pos hphi_pos hlogu_pos)]
    calc (Q : ℝ) * ((q.totient : ℝ) * Real.log u)
        = (q.totient : ℝ) * ((Q : ℝ) * Real.log u) := by ring
      _ ≤ (q : ℝ) * ((6 / 5 : ℝ) * u) := mul_le_mul hphi_le h1 (by positivity) hq_pos.le
      _ ≤ (6 / 5 : ℝ) * (y : ℝ) * (q : ℝ) := by nlinarith
  have hterm3 : (1 : ℝ) ≤ (3 / 10 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have hlog9' : Real.log (9 : ℝ) ≤ (23 : ℝ) / 10 := by
      have h4 : Real.log ((9 : ℝ) ^ (4 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (13 : ℕ)) :=
        Real.log_le_log (by positivity) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at h4
      push_cast at h4
      have hl2 : Real.log 2 < (694 : ℝ) / 1000 := by linarith [Real.log_two_lt_d9]
      linarith
    have hlogu_lin : Real.log u ≤ (3 / 10 : ℝ) * u := by
      have hstep := Real.log_le_sub_one_of_pos (div_pos hu_pos (by norm_num : (0 : ℝ) < 9))
      rw [Real.log_div hu_pos.ne' (by norm_num : (9 : ℝ) ≠ 0)] at hstep
      linarith
    rw [le_div_iff₀ (mul_pos hphi_pos hlogu_pos), one_mul]
    have hqy : (q : ℝ) * u = (y : ℝ) := by dsimp only [u]; field_simp [hq_pos.ne']
    calc (q.totient : ℝ) * Real.log u
        ≤ (q : ℝ) * ((3 / 10 : ℝ) * u) := mul_le_mul hphi_le hlogu_lin hlogu_pos.le hq_pos.le
      _ = (3 / 10 : ℝ) * (y : ℝ) := by rw [← hqy]; ring
  have hsum_const : (76 / 9 : ℝ) + ((6 / 5 : ℝ) + (3 / 10 : ℝ)) ≤ 10 := by norm_num
  have hcomb :
      (76 / 9 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
        ((6 / 5 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
         (3 / 10 : ℝ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u)) ≤
      10 * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    rw [← add_div, ← add_div, ← add_mul, ← add_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsum_const (Nat.cast_nonneg _)) (mul_pos hphi_pos hlogu_pos).le
  linarith

/-- Bridge to `Stage2DirichletAP.primeCountAP`: unconditional Brun–Titchmarsh upper bound for
`primeCountAP q a (x + y) - primeCountAP q a x`. -/
theorem brun_titchmarsh_primeCountAP {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    (x y : ℕ) (hy : 9 * q ≤ y) :
    ((Stage2DirichletAP.primeCountAP q a ((x + y : ℕ) : ℝ) -
        Stage2DirichletAP.primeCountAP q a (x : ℝ) : ℕ) : ℝ) ≤
      10 * (y : ℝ) / ((q.totient : ℝ) * Real.log ((y : ℝ) / (q : ℝ))) := by
  have hcard :
      Stage2DirichletAP.primeCountAP q a ((x + y : ℕ) : ℝ) -
          Stage2DirichletAP.primeCountAP q a (x : ℝ) =
        ((Finset.Ioc x (x + y)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card := by
    unfold Stage2DirichletAP.primeCountAP
    simp only [Nat.floor_natCast]
    have hsub :
        (Finset.range (x + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) ⊆
          (Finset.range (x + y + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]) :=
      Finset.filter_subset_filter _ (Finset.range_mono (by omega))
    rw [← Finset.card_sdiff_of_subset hsub]
    congr 1
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, by omega⟩, h2⟩
      by_contra hle
      exact h3 ⟨by omega, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h3⟩, fun h => by omega⟩
  rw [hcard]
  exact brun_titchmarsh_ap hq hcop x y hy

/-- **Sharp Asymptotic Brun–Titchmarsh Prime Bound in Arithmetic Progressions (`(2 + ε)`)**:
for every `ε > 0`, there exists `U₀ : ℕ` such that for all `q ≥ 1`, `Nat.Coprime a q`, and
`y ≥ U₀ * q`, `π(x + y; q, a) - π(x; q, a) ≤ (2 + ε) * y / (φ(q) * log (y / q))`. -/
theorem brun_titchmarsh_ap_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ U₀ : ℕ, ∀ {q a : ℕ}, 0 < q → Nat.Coprime a q → ∀ x y : ℕ, U₀ * q ≤ y →
      (((Finset.Ioc x (x + y)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) ≤
        (2 + ε) * (y : ℝ) / ((q.totient : ℝ) * Real.log ((y : ℝ) / (q : ℝ))) := by
  set δ : ℝ := min (1 / 4) (ε / 12)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le_quarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδ_le_eps : δ ≤ ε / 12 := min_le_right _ _
  set L₀ : ℝ := max (max 4 (2 / δ)) ((2 / δ) * max 0 (Real.log (6 / δ)))
  set U₁ : ℝ := max (max (Real.exp L₀) (2 / δ))
    (max ((2 / (3 * δ ^ 2)) * max 0 (Real.log (2 / (3 * δ ^ 2))))
         ((2 / δ) * max 0 (Real.log (2 / δ))))
  refine ⟨max 16 ⌈U₁⌉₊, fun {q a} hq hcop x y hy => ?_⟩
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hphi_le : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  set u : ℝ := (y : ℝ) / (q : ℝ)
  have hu_ge16 : 16 ≤ u := (le_div_iff₀ hq_pos).mpr (by
    exact_mod_cast (Nat.mul_le_mul_right q (le_max_left 16 ⌈U₁⌉₊)).trans hy)
  have hu_geU₁ : U₁ ≤ u := (le_div_iff₀ hq_pos).mpr <| by
    have h1 : (⌈U₁⌉₊ : ℝ) * (q : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_right q (le_max_right 16 ⌈U₁⌉₊)).trans hy
    exact (mul_le_mul_of_nonneg_right (Nat.le_ceil U₁) hq_pos.le).trans h1
  have hu_pos : 0 < u := by linarith
  have hL_ge : L₀ ≤ Real.log u := by
    have hexp : Real.exp L₀ ≤ u := ((le_max_left _ _).trans (le_max_left _ _)).trans hu_geU₁
    have h := Real.log_le_log (Real.exp_pos L₀) hexp
    rwa [Real.log_exp] at h
  have hlogu_ge4 : 4 ≤ Real.log u := ((le_max_left 4 _).trans (le_max_left _ _)).trans hL_ge
  have hlogu_pos : 0 < Real.log u := by linarith
  have h1_le_du : 1 ≤ (δ / 2) * u := by
    have h1 : 2 / δ ≤ u := ((le_max_right _ _).trans (le_max_left _ _)).trans hu_geU₁
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ δ / 2)
    have h3 : (δ / 2) * (2 / δ) = 1 := by field_simp [hδ_pos.ne']
    linarith
  have hlogu_inv : 1 / Real.log u ≤ δ / 2 := by
    rw [div_le_iff₀ hlogu_pos]
    have h1 : 2 / δ ≤ Real.log u := ((le_max_right 4 _).trans (le_max_left _ _)).trans hL_ge
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ δ / 2)
    have h3 : (δ / 2) * (2 / δ) = 1 := by field_simp [hδ_pos.ne']
    linarith
  have hlog_3log : Real.log (3 * Real.log u) ≤ δ * Real.log u := by
    refine log_mul_le_linear (a := 3) (by norm_num) hδ_pos hlogu_pos ?_
    rw [show 2 * (3 : ℝ) / δ = 6 / δ by ring]
    exact (le_max_right _ _).trans hL_ge
  have hlog_le_3d2u : Real.log u ≤ 3 * δ ^ 2 * u := by
    have h := log_mul_le_linear (a := 1) (δ := 3 * δ ^ 2) zero_lt_one (by positivity) hu_pos (by
      rw [show 2 * (1 : ℝ) / (3 * δ ^ 2) = 2 / (3 * δ ^ 2) by ring]
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans hu_geU₁)
    simpa using h
  have hlog_le_du : Real.log u ≤ δ * u := by
    have h := log_mul_le_linear (a := 1) (δ := δ) zero_lt_one hδ_pos hu_pos (by
      rw [show 2 * (1 : ℝ) / δ = 2 / δ by ring]
      exact ((le_max_right _ _).trans (le_max_right _ _)).trans hu_geU₁)
    simpa using h
  set R : ℝ := Real.sqrt (u / (3 * Real.log u))
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  set Q : ℕ := ⌊R⌋₊
  have hQ_ge1 : 1 ≤ Q := by
    refine Nat.le_floor (Real.le_sqrt_of_sq_le ?_)
    rw [Nat.cast_one, one_pow, le_div_iff₀ (by positivity)]
    have : 9 * δ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hQ_le : (Q : ℝ) ≤ R := Nat.floor_le hR_pos.le
  have hQ_gt : R < (Q : ℝ) + 1 := Nat.lt_floor_add_one R
  have h3Q2 : 3 * (Q : ℝ) ^ 2 ≤ (δ / 2) * u := by
    have h1 : (Q : ℝ) ^ 2 ≤ u / (3 * Real.log u) := by
      calc (Q : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
        _ = u / (3 * Real.log u) := Real.sq_sqrt (by positivity)
    have h2 : 3 * (Q : ℝ) ^ 2 ≤ u / Real.log u := by
      have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
      refine hmul.trans_eq ?_
      field_simp [hlogu_pos.ne']
    calc 3 * (Q : ℝ) ^ 2 ≤ u * (1 / Real.log u) := by rwa [mul_one_div]
      _ ≤ u * (δ / 2) := mul_le_mul_of_nonneg_left hlogu_inv hu_pos.le
      _ = (δ / 2) * u := mul_comm _ _
  have hlogQ1 : (1 - δ) / 2 * Real.log u ≤ Real.log ((Q : ℝ) + 1) := by
    have h1 : Real.log R ≤ Real.log ((Q : ℝ) + 1) := Real.log_le_log hR_pos hQ_gt.le
    rw [show Real.log R = (Real.log u - Real.log (3 * Real.log u)) / 2 by
      dsimp only [R]
      rw [Real.log_sqrt (by positivity), Real.log_div hu_pos.ne' (by positivity)]] at h1
    linarith
  have hlogQ1_pos : 0 < Real.log ((Q : ℝ) + 1) := by nlinarith
  have hraw := brun_titchmarsh_ap_raw hq hcop x y Q hQ_ge1
  have hdiv_le : ((y / q : ℕ) : ℝ) ≤ u :=
    (le_div_iff₀ hq_pos).mpr (by exact_mod_cast Nat.div_mul_le_self y q)
  have hterm1 :
      ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
        (2 * (1 + δ) / (1 - δ)) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have h1d : 0 < 1 - δ := by linarith
    have hnum : ((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2 ≤ (1 + δ) * u := by linarith
    have hstep1 : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) ≤
        (1 + δ) * (y : ℝ) / (q.totient : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hnum (div_nonneg hq_pos.le hphi_pos.le)
      refine hmul.trans_eq ?_
      dsimp only [u]; field_simp [hq_pos.ne', hphi_pos.ne']
    rw [div_le_div_iff₀ hlogQ1_pos (mul_pos hphi_pos hlogu_pos)]
    have hstep2 : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) * (q.totient : ℝ) ≤
        (1 + δ) * (y : ℝ) := by
      have := mul_le_mul_of_nonneg_right hstep1 hphi_pos.le
      rwa [div_mul_cancel₀ _ hphi_pos.ne'] at this
    have hlhs : ((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) *
        ((q.totient : ℝ) * Real.log u) ≤ (1 + δ) * (y : ℝ) * Real.log u := by
      calc _ = (((q : ℝ) / (q.totient : ℝ)) * (((y / q : ℕ) : ℝ) + 1 + 3 * (Q : ℝ) ^ 2) * (q.totient : ℝ)) * Real.log u := by ring
        _ ≤ (1 + δ) * (y : ℝ) * Real.log u := mul_le_mul_of_nonneg_right hstep2 hlogu_pos.le
    have hrhs : (1 + δ) * (y : ℝ) * Real.log u ≤
        (2 * (1 + δ) / (1 - δ)) * (y : ℝ) * Real.log ((Q : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hlogQ1 (by positivity : 0 ≤ (2 * (1 + δ) / (1 - δ)) * (y : ℝ))
      refine le_trans ?_ hmul
      have : (2 * (1 + δ) / (1 - δ)) * (y : ℝ) * ((1 - δ) / 2 * Real.log u) =
          (1 + δ) * (y : ℝ) * Real.log u := by
        field_simp [h1d.ne']
      linarith
    exact hlhs.trans hrhs
  have hterm2 : ((Q / q : ℕ) : ℝ) ≤ δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have hQdiv : ((Q / q : ℕ) : ℝ) ≤ (Q : ℝ) / (q : ℝ) :=
      (le_div_iff₀ hq_pos).mpr (by exact_mod_cast Nat.div_mul_le_self Q q)
    have hQlog : (Q : ℝ) * Real.log u ≤ δ * u := by
      have hsq : ((Q : ℝ) * Real.log u) ^ 2 ≤ (δ * u) ^ 2 := by
        have hq2 : (Q : ℝ) ^ 2 ≤ u / (3 * Real.log u) := by
          calc (Q : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
            _ = u / (3 * Real.log u) := Real.sq_sqrt (by positivity)
        calc ((Q : ℝ) * Real.log u) ^ 2
            = (Q : ℝ) ^ 2 * (Real.log u) ^ 2 := mul_pow _ _ 2
          _ ≤ (u / (3 * Real.log u)) * (Real.log u) ^ 2 :=
              mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
          _ = u * Real.log u / 3 := by field_simp [hlogu_pos.ne']
          _ ≤ u * (3 * δ ^ 2 * u) / 3 := by gcongr
          _ = (δ * u) ^ 2 := by ring
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) Q) hlogu_pos.le, mul_nonneg hδ_pos.le hu_pos.le]
    have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hu_le_y : u ≤ (y : ℝ) := by dsimp only [u]; exact div_le_self (Nat.cast_nonneg _) hq_ge1
    refine hQdiv.trans ?_
    rw [div_le_div_iff₀ hq_pos (mul_pos hphi_pos hlogu_pos)]
    calc (Q : ℝ) * ((q.totient : ℝ) * Real.log u)
        = (q.totient : ℝ) * ((Q : ℝ) * Real.log u) := by ring
      _ ≤ (q : ℝ) * (δ * u) := mul_le_mul hphi_le hQlog (by positivity) hq_pos.le
      _ = δ * (q : ℝ) * u := by ring
      _ ≤ δ * (q : ℝ) * (y : ℝ) := mul_le_mul_of_nonneg_left hu_le_y (by positivity)
      _ = δ * (y : ℝ) * (q : ℝ) := by ring
  have hterm3 : (1 : ℝ) ≤ δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    rw [le_div_iff₀ (mul_pos hphi_pos hlogu_pos), one_mul]
    have hqy : (q : ℝ) * u = (y : ℝ) := by dsimp only [u]; field_simp [hq_pos.ne']
    calc (q.totient : ℝ) * Real.log u
        ≤ (q : ℝ) * (δ * u) := mul_le_mul hphi_le hlog_le_du hlogu_pos.le hq_pos.le
      _ = δ * (y : ℝ) := by rw [← hqy]; ring
  have hconst : 2 * (1 + δ) / (1 - δ) + 2 * δ ≤ 2 + ε := by
    have h1d : (3 : ℝ) / 4 ≤ 1 - δ := by linarith
    have h1 : 2 * (1 + δ) / (1 - δ) = 2 + 4 * δ / (1 - δ) := by
      field_simp [(by linarith : 1 - δ ≠ 0)]; ring
    have h2 : 4 * δ / (1 - δ) ≤ 16 / 3 * δ := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - δ)]
      nlinarith
    linarith
  have hcomb :
      (2 * (1 + δ) / (1 - δ)) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
        (δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
         δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u)) ≤
      (2 + ε) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by
    have hlhs :
        (2 * (1 + δ) / (1 - δ)) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
          (δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u) +
           δ * (y : ℝ) / ((q.totient : ℝ) * Real.log u)) =
        (2 * (1 + δ) / (1 - δ) + 2 * δ) * (y : ℝ) / ((q.totient : ℝ) * Real.log u) := by ring
    rw [hlhs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg _)) (mul_pos hphi_pos hlogu_pos).le
  linarith

/-! ## Section 4: Selberg's Optimal Upper-Bound Sieve (Möbius Diagonalization) -/

/-- Completely multiplicative Selberg density function `g : ℕ → ℝ` with `g(p) ∈ (0, 1)` on primes. -/
def IsSelbergDensity (g : ℕ → ℝ) : Prop :=
  g 1 = 1 ∧ (∀ a b : ℕ, g (a * b) = g a * g b) ∧ (∀ p : ℕ, p.Prime → 0 < g p ∧ g p < 1)

/-- Selberg auxiliary multiplicative weight `f(r) = ∏_{p ∣ r} (1 / g(p) - 1)`. -/
def selbergF (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (1 / g p - 1)

/-- Selberg denominator `G(z) = ∑_{1 ≤ r ≤ z, Squarefree r} 1 / f(r)`. -/
def selbergG (g : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, 1 / selbergF g r

/-- Selberg quadratic form `Q(λ) = ∑_{d₁, d₂ ≤ z} λ_{d₁} λ_{d₂} g([d₁, d₂])`. -/
def selbergQuadForm (z : ℕ) (g lam : ℕ → ℝ) : ℝ :=
  ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)

/-- Selberg Möbius change of variables `y_r = μ(r) * f(r) * ∑_{d ≤ z, r ∣ d} λ_d g(d)`. -/
def selbergY (z : ℕ) (g lam : ℕ → ℝ) (r : ℕ) : ℝ :=
  (ArithmeticFunction.moebius r : ℝ) * selbergF g r *
    ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d

/-- Explicit optimal Selberg sieve weights `λ*_d`. -/
def selbergOptLam (z : ℕ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 1 z then
    ((ArithmeticFunction.moebius d : ℝ) / (g d * selbergG g z)) *
      ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ d ∣ m), 1 / selbergF g m
  else 0

theorem selbergF_one (g : ℕ → ℝ) : selbergF g 1 = 1 := by
  simp [selbergF]

theorem selbergF_pos {g : ℕ → ℝ} (hg : IsSelbergDensity g) (r : ℕ) :
    0 < selbergF g r := by
  unfold selbergF
  refine Finset.prod_pos fun p hp => ?_
  obtain ⟨h0, h1⟩ := hg.2.2 p (Nat.prime_of_mem_primeFactors hp)
  have : 1 < 1 / g p := (one_lt_div h0).mpr h1
  linarith

theorem selbergF_mul_coprime (g : ℕ → ℝ) {a b : ℕ}
    (hcop : Nat.Coprime a b) :
    selbergF g (a * b) = selbergF g a * selbergF g b := by
  unfold selbergF
  rw [Nat.Coprime.primeFactors_mul hcop, Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]

theorem selberg_density_pos_of_pos {g : ℕ → ℝ} (hg : IsSelbergDensity g) {n : ℕ} (hn : 0 < n) :
    0 < g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1; rw [hg.1]; exact zero_lt_one
    · set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpd : p ∣ n := Nat.minFac_dvd n
      set m : ℕ := n / p
      have hnm : n = p * m := (Nat.mul_div_cancel' hpd).symm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hnm; omega
      have hm_lt : m < n := by have := hp.two_le; nlinarith
      rw [hnm, hg.2.1]
      exact mul_pos (hg.2.2 p hp).1 (ih m hm_lt hm_pos)

theorem selberg_density_eq_prod_of_squarefree {g : ℕ → ℝ} (hg : IsSelbergDensity g)
    {n : ℕ} (hn : Squarefree n) :
    g n = ∏ p ∈ n.primeFactors, g p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1; simp [hg.1]
    · set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      have hpd : p ∣ n := Nat.minFac_dvd n
      set m : ℕ := n / p
      have hnm : n = p * m := (Nat.mul_div_cancel' hpd).symm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hnm; exact hn.ne_zero hnm
      have hm_lt : m < n := by have := hp.two_le; nlinarith
      have hndvd : ¬ p ∣ m := fun hpm =>
        hp.ne_one (Nat.isUnit_iff.mp (hn p (by obtain ⟨k, hk⟩ := hpm; exact ⟨k, by rw [hnm, hk]; ring⟩)))
      have hm_sqf : Squarefree m := hn.squarefree_of_dvd ⟨p, by rw [hnm, mul_comm]⟩
      have hp_not_m : p ∉ m.primeFactors := fun h => hndvd (Nat.dvd_of_mem_primeFactors h)
      have hpf : n.primeFactors = insert p m.primeFactors := by
        ext r
        simp only [Nat.mem_primeFactors, Finset.mem_insert]
        constructor
        · rintro ⟨hr, hrdvd, -⟩
          rw [hnm] at hrdvd
          rcases hr.dvd_mul.mp hrdvd with hrp | hrm
          · left; exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
          · right; exact ⟨hr, hrm, hm_pos.ne'⟩
        · rintro (rfl | ⟨hr, hrm, -⟩)
          · exact ⟨hp, hpd, hn.ne_zero⟩
          · exact ⟨hr, hrm.trans ⟨p, by rw [hnm, mul_comm]⟩, hn.ne_zero⟩
      rw [hpf, Finset.prod_insert hp_not_m, ← ih m hm_lt hm_sqf, hnm, hg.2.1]

/-- Key squarefree divisor identity: `1 / g(m) = ∑_{r ∣ m} f(r)` for squarefree `m`. -/
theorem inv_selberg_density_eq_sum_divisors {g : ℕ → ℝ} (hg : IsSelbergDensity g)
    {m : ℕ} (hm : Squarefree m) :
    1 / g m = ∑ r ∈ m.divisors, selbergF g r := by
  have h1 : 1 / g m = ∏ p ∈ m.primeFactors, (1 + (1 / g p - 1)) := by
    rw [selberg_density_eq_prod_of_squarefree hg hm, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => by ring
  rw [h1, Finset.prod_one_add]
  refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
  · intro S hS
    have hsub := Finset.mem_powerset.mp hS
    exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset S m.primeFactors id hsub).trans
      (Nat.prod_primeFactors_dvd m), hm.ne_zero⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    have hsub₁ := Finset.mem_powerset.mp hS₁
    have hsub₂ := Finset.mem_powerset.mp hS₂
    have hpf : ∀ S ⊆ m.primeFactors, (∏ p ∈ S, p).primeFactors = S := by
      intro S hsub
      ext r
      simp only [Nat.mem_primeFactors]
      constructor
      · rintro ⟨hr, hdvd, -⟩
        obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
        rwa [(Nat.prime_dvd_prime_iff_eq hr (Nat.prime_of_mem_primeFactors (hsub hp))).mp hrp]
      · intro hr
        exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr,
          (squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero⟩
    rw [← hpf S₁ hsub₁, ← hpf S₂ hsub₂, heq]
  · intro r hr
    obtain ⟨hrm, -⟩ := Nat.mem_divisors.mp hr
    have hr_sqf : Squarefree r := hm.squarefree_of_dvd hrm
    exact ⟨r.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hrm hm.ne_zero),
      Nat.prod_primeFactors_of_squarefree hr_sqf⟩
  · intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hpf : (∏ p ∈ S, p).primeFactors = S := by
      ext r
      simp only [Nat.mem_primeFactors]
      constructor
      · rintro ⟨hr, hdvd, -⟩
        obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
        rwa [(Nat.prime_dvd_prime_iff_eq hr (Nat.prime_of_mem_primeFactors (hsub hp))).mp hrp]
      · intro hr
        exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr,
          (squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero⟩
    unfold selbergF
    rw [hpf]

theorem one_le_selbergG {g : ℕ → ℝ} (hg : IsSelbergDensity g) {z : ℕ} (hz : 1 ≤ z) :
    1 ≤ selbergG g z := by
  unfold selbergG
  have h1 : (1 : ℕ) ∈ (Finset.Icc 1 z).filter Squarefree :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hz⟩, squarefree_one⟩
  calc (1 : ℝ) = 1 / selbergF g 1 := by simp [selbergF_one]
    _ ≤ ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, 1 / selbergF g r :=
        Finset.single_le_sum (fun r _ => div_nonneg zero_le_one (selbergF_pos hg r).le) h1

private theorem moebius_sq_eq_one_of_squarefree {r : ℕ} (hr : Squarefree r) :
    (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
  have h : (ArithmeticFunction.moebius r : ℤ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hr]
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  exact_mod_cast h

private theorem moebius_eq_zero_of_not_squarefree {r : ℕ} (hr : ¬ Squarefree r) :
    (ArithmeticFunction.moebius r : ℝ) = 0 := by
  have h : ArithmeticFunction.moebius r = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hr
  exact_mod_cast h

private theorem sum_divisors_moebius_eq_zero_of_ne_one {n : ℕ} (hn : n ≠ 1) :
    ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℝ) = 0 := by
  have hZ : ∑ r ∈ n.divisors, (ArithmeticFunction.moebius r : ℤ) = 0 := by
    have hmul : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
        (1 : ArithmeticFunction ℤ) n :=
      congrArg (fun f => f n) ArithmeticFunction.moebius_mul_coe_zeta
    rw [ArithmeticFunction.one_apply, if_neg hn, ArithmeticFunction.mul_apply] at hmul
    rw [← hmul]
    refine Finset.sum_bij (fun d _ => (d, n / d)) ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hdn, hn0⟩
    · intro d₁ _ d₂ _ h
      exact (Prod.mk.inj h).1
    · intro x hx
      obtain ⟨hab, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have ha0 : 0 < x.1 := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hab; exact hn0 hab.symm
      exact ⟨x.1, Nat.mem_divisors.mpr ⟨⟨x.2, hab.symm⟩, hn0⟩, Prod.ext rfl (Nat.eq_div_of_mul_eq_right ha0.ne' hab).symm⟩
    · intro d hd
      obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
      have hne0 : n / d ≠ 0 := fun h0 => hn0 (by rw [← Nat.mul_div_cancel' hdn, h0, mul_zero])
      simp [ArithmeticFunction.zeta_apply, hne0]
  exact_mod_cast hZ

/-- **Exact Selberg Diagonalization Identity**:
for any completely multiplicative Selberg density `g` and any squarefree-supported `λ`,
`∑_{d₁, d₂ ≤ z} λ_{d₁} λ_{d₂} g([d₁, d₂]) = ∑_{r ≤ z} y_r² / f(r)`. -/
theorem selberg_diagonalization {z : ℕ} {g lam : ℕ → ℝ} (hg : IsSelbergDensity g)
    (hsupp : ∀ d, ¬ Squarefree d → lam d = 0) :
    selbergQuadForm z g lam =
      ∑ r ∈ Finset.Icc 1 z, (selbergY z g lam r) ^ 2 / selbergF g r := by
  unfold selbergQuadForm
  have hstep1 :
      ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂) =
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
            if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0 := by
    refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
    by_cases hsqf₁ : Squarefree d₁
    · by_cases hsqf₂ : Squarefree d₂
      · set m : ℕ := Nat.gcd d₁ d₂
        have hm_sqf : Squarefree m := hsqf₁.squarefree_of_dvd (Nat.gcd_dvd_left d₁ d₂)
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sqf.ne_zero
        have hgm_pos : 0 < g m := selberg_density_pos_of_pos hg hm_pos
        have hlcm : g (Nat.lcm d₁ d₂) = g d₁ * g d₂ * (1 / g m) := by
          have hprod : g m * g (Nat.lcm d₁ d₂) = g d₁ * g d₂ := by
            rw [← hg.2.1, Nat.gcd_mul_lcm, hg.2.1]
          field_simp [hgm_pos.ne']
          linarith
        rw [hlcm, inv_selberg_density_eq_sum_divisors hg hm_sqf]
        have hsum_eq :
            ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
              (if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0) =
            ∑ r ∈ m.divisors, selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext r
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨⟨_, _⟩, _⟩, h1, h2⟩
            exact ⟨Nat.dvd_gcd h1 h2, hm_pos.ne'⟩
          · rintro ⟨hrm, -⟩
            have hr_d1 : r ∣ d₁ := hrm.trans (Nat.gcd_dvd_left d₁ d₂)
            have hr_d2 : r ∣ d₂ := hrm.trans (Nat.gcd_dvd_right d₁ d₂)
            have hr_sqf : Squarefree r := hm_sqf.squarefree_of_dvd hrm
            have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_sqf.ne_zero
            have hd1_pos : 0 < d₁ := (Finset.mem_Icc.mp hd₁).1
            have hr_le : r ≤ z := (Nat.le_of_dvd hd1_pos hr_d1).trans (Finset.mem_Icc.mp hd₁).2
            exact ⟨⟨⟨hr_pos, hr_le⟩, hr_sqf⟩, hr_d1, hr_d2⟩
        rw [hsum_eq, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      · rw [hsupp d₂ hsqf₂]
        simp
    · rw [hsupp d₁ hsqf₁]
      simp
  rw [hstep1]
  -- Swap sums to put `r` outermost
  have hswap :
      ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
        ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
          (if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0) =
      ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
        selbergF g r * (∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d) ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ d₂ ∈ Finset.Icc 1 z, ∑ d₁ ∈ Finset.Icc 1 z,
            ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
              (if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0)
        = ∑ d₂ ∈ Finset.Icc 1 z, ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
            ∑ d₁ ∈ Finset.Icc 1 z,
              (if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ Finset.Icc 1 z,
            ∑ d₁ ∈ Finset.Icc 1 z,
              (if r ∣ d₁ ∧ r ∣ d₂ then selbergF g r * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0) :=
          Finset.sum_comm
      _ = ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
            selbergF g r * (∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun d₂ _ => ?_
          by_cases hr2 : r ∣ d₂
          · rw [if_pos hr2, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d₁ _ => ?_
            by_cases hr1 : r ∣ d₁
            · rw [if_pos ⟨hr1, hr2⟩, if_pos hr1]; ring
            · rw [if_neg (fun h => hr1 h.1), if_neg hr1]
          · rw [if_neg hr2]
            exact Finset.sum_eq_zero fun d₁ _ => if_neg (fun h => hr2 h.2)
  rw [hswap, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold selbergY
  by_cases hsqf : Squarefree r
  · rw [if_pos hsqf]
    have hmu2 := moebius_sq_eq_one_of_squarefree hsqf
    have hfpos := selbergF_pos hg r
    field_simp [hfpos.ne']
    rw [hmu2, mul_one]
  · rw [if_neg hsqf, moebius_eq_zero_of_not_squarefree hsqf]
    simp

/-- Exact Möbius linear constraint: `∑_{r ≤ z} y_r / f(r) = λ_1` for `z ≥ 1`. -/
theorem selberg_linear_constraint {z : ℕ} (hz : 1 ≤ z) {g lam : ℕ → ℝ} (hg : IsSelbergDensity g) :
    ∑ r ∈ Finset.Icc 1 z, selbergY z g lam r / selbergF g r = lam 1 := by
  have h1 : ∑ r ∈ Finset.Icc 1 z, selbergY z g lam r / selbergF g r =
      ∑ r ∈ Finset.Icc 1 z, (ArithmeticFunction.moebius r : ℝ) *
        ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d := by
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold selbergY
    have hfpos := selbergF_pos hg r
    field_simp [hfpos.ne']
  rw [h1]
  have h2 :
      ∑ r ∈ Finset.Icc 1 z, (ArithmeticFunction.moebius r : ℝ) *
        ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d =
      ∑ d ∈ Finset.Icc 1 z, lam d * g d *
        ∑ r ∈ d.divisors, (ArithmeticFunction.moebius r : ℝ) := by
    calc ∑ r ∈ Finset.Icc 1 z, (ArithmeticFunction.moebius r : ℝ) *
            ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), lam d * g d
        = ∑ r ∈ Finset.Icc 1 z, ∑ d ∈ Finset.Icc 1 z,
            if r ∣ d then (ArithmeticFunction.moebius r : ℝ) * (lam d * g d) else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum, Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 z, ∑ r ∈ Finset.Icc 1 z,
            if r ∣ d then (ArithmeticFunction.moebius r : ℝ) * (lam d * g d) else 0 :=
          Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 z, lam d * g d * ∑ r ∈ d.divisors, (ArithmeticFunction.moebius r : ℝ) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          have hfilt : (Finset.Icc 1 z).filter (fun r => r ∣ d) = d.divisors := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
            have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
            have hd_le : d ≤ z := (Finset.mem_Icc.mp hd).2
            constructor
            · rintro ⟨_, hrd⟩; exact ⟨hrd, hd_pos.ne'⟩
            · rintro ⟨hrd, -⟩
              exact ⟨⟨Nat.pos_of_dvd_of_pos hrd hd_pos, (Nat.le_of_dvd hd_pos hrd).trans hd_le⟩, hrd⟩
          rw [hfilt]
          refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [h2, Finset.sum_eq_single 1]
  · simp [hg.1]
  · intro d _ hd1
    rw [sum_divisors_moebius_eq_zero_of_ne_one hd1, mul_zero]
  · intro h1not; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hz⟩) h1not

/-- **Exact Selberg Completing-the-Square Identity**:
when `λ_1 = 1` (and `λ` is squarefree-supported),
`Q(λ) = 1 / G(z) + ∑_{r ≤ z, Squarefree r} (y_r - 1 / G(z))² / f(r)`. -/
theorem selberg_completing_square {z : ℕ} (hz : 1 ≤ z) {g lam : ℕ → ℝ} (hg : IsSelbergDensity g)
    (hsupp : ∀ d, ¬ Squarefree d → lam d = 0) (hlam1 : lam 1 = 1) :
    selbergQuadForm z g lam =
      1 / selbergG g z +
        ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
          (selbergY z g lam r - 1 / selbergG g z) ^ 2 / selbergF g r := by
  have hGpos : 0 < selbergG g z := lt_of_lt_of_le zero_lt_one (one_le_selbergG hg hz)
  rw [selberg_diagonalization hg hsupp]
  have hlin : ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, selbergY z g lam r / selbergF g r = 1 := by
    rw [← hlam1, ← selberg_linear_constraint hz hg (lam := lam), Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hsqf : Squarefree r
    · rw [if_pos hsqf]
    · rw [if_neg hsqf]; unfold selbergY; rw [moebius_eq_zero_of_not_squarefree hsqf]; simp
  have hdiag : ∑ r ∈ Finset.Icc 1 z, (selbergY z g lam r) ^ 2 / selbergF g r =
      ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (selbergY z g lam r) ^ 2 / selbergF g r := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hsqf : Squarefree r
    · rw [if_pos hsqf]
    · rw [if_neg hsqf]; unfold selbergY; rw [moebius_eq_zero_of_not_squarefree hsqf]; simp
  rw [hdiag]
  have hexp :
      ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
        (selbergY z g lam r - 1 / selbergG g z) ^ 2 / selbergF g r =
      (∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (selbergY z g lam r) ^ 2 / selbergF g r) -
        (2 / selbergG g z) * (∑ r ∈ (Finset.Icc 1 z).filter Squarefree, selbergY z g lam r / selbergF g r) +
        (1 / selbergG g z) ^ 2 * (∑ r ∈ (Finset.Icc 1 z).filter Squarefree, 1 / selbergF g r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hexp, hlin, show ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, 1 / selbergF g r = selbergG g z from rfl]
  field_simp [hGpos.ne']
  ring

/-- **Selberg Quadratic-Form Lower Bound**: `1 / G(z) ≤ Q(λ)` for all squarefree-supported `λ` with `λ_1 = 1`. -/
theorem selberg_quadratic_lower_bound {z : ℕ} (hz : 1 ≤ z) {g lam : ℕ → ℝ} (hg : IsSelbergDensity g)
    (hsupp : ∀ d, ¬ Squarefree d → lam d = 0) (hlam1 : lam 1 = 1) :
    1 / selbergG g z ≤ selbergQuadForm z g lam := by
  rw [selberg_completing_square hz hg hsupp hlam1]
  have hnn : 0 ≤ ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
      (selbergY z g lam r - 1 / selbergG g z) ^ 2 / selbergF g r :=
    Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (selbergF_pos hg r).le
  linarith

/-- Optimal Selberg weights satisfy `λ*_1 = 1` and vanish off squarefree integers. -/
theorem selbergOptLam_one {z : ℕ} (hz : 1 ≤ z) {g : ℕ → ℝ} (hg : IsSelbergDensity g) :
    selbergOptLam z g 1 = 1 := by
  have hGpos : 0 < selbergG g z := lt_of_lt_of_le zero_lt_one (one_le_selbergG hg hz)
  unfold selbergOptLam
  rw [if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hz⟩), ArithmeticFunction.moebius_apply_one, Int.cast_one, hg.1]
  have hfilt : (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ 1 ∣ m) =
      (Finset.Icc 1 z).filter Squarefree := by
    ext m; simp
  rw [hfilt]
  change (1 / (1 * selbergG g z)) * selbergG g z = 1
  field_simp [hGpos.ne']

theorem selbergOptLam_eq_zero_of_not_squarefree (z : ℕ) (g : ℕ → ℝ) (d : ℕ) (hd : ¬ Squarefree d) :
    selbergOptLam z g d = 0 := by
  unfold selbergOptLam
  split_ifs
  · rw [moebius_eq_zero_of_not_squarefree hd]; simp
  · rfl

/-- Exact evaluation of `selbergY` at the optimal weights `λ*`:
`y_r(λ*) = μ(r)² / G(z)` and `y_r(λ*) / f(r) = μ(r)² / (f(r) * G(z))`. -/
theorem selbergY_optLam {z : ℕ} (hz : 1 ≤ z) {g : ℕ → ℝ} (hg : IsSelbergDensity g)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 z) :
    selbergY z g (selbergOptLam z g) r =
      ((ArithmeticFunction.moebius r : ℝ) ^ 2) / selbergG g z := by
  have hGpos : 0 < selbergG g z := lt_of_lt_of_le zero_lt_one (one_le_selbergG hg hz)
  unfold selbergY
  by_cases hrsqf : Squarefree r
  · have hsum : ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), selbergOptLam z g d * g d =
        (ArithmeticFunction.moebius r : ℝ) / (selbergF g r * selbergG g z) := by
      have h1 :
          ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d), selbergOptLam z g d * g d =
          (1 / selbergG g z) *
            ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d),
              (ArithmeticFunction.moebius d : ℝ) *
                ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ d ∣ m), 1 / selbergF g m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdI : d ∈ Finset.Icc 1 z := (Finset.mem_filter.mp hd).1
        have hgd : 0 < g d := selberg_density_pos_of_pos hg (Finset.mem_Icc.mp hdI).1
        unfold selbergOptLam
        rw [if_pos hdI]
        field_simp [hgd.ne', hGpos.ne']
      rw [h1]
      -- Swap `d` and `m` (`r ∣ d ∣ m`)
      have hswap :
          ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d),
            (ArithmeticFunction.moebius d : ℝ) *
              ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ d ∣ m), 1 / selbergF g m =
          ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ r ∣ m),
            (1 / selbergF g m) *
              ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius d : ℝ) := by
        calc ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d),
              (ArithmeticFunction.moebius d : ℝ) *
                ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ d ∣ m), 1 / selbergF g m
            = ∑ d ∈ Finset.Icc 1 z, ∑ m ∈ (Finset.Icc 1 z).filter Squarefree,
                if r ∣ d ∧ d ∣ m then (ArithmeticFunction.moebius d : ℝ) * (1 / selbergF g m) else 0 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun d _ => ?_
              by_cases hrd : r ∣ d
              · rw [if_pos hrd, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
                refine Finset.sum_congr rfl fun m _ => ?_
                by_cases hmsqf : Squarefree m
                · by_cases hdm : d ∣ m
                  · rw [if_pos ⟨hmsqf, hdm⟩, if_pos hmsqf, if_pos ⟨hrd, hdm⟩]
                  · rw [if_neg (fun h => hdm h.2), if_pos hmsqf, if_neg (fun h => hdm h.2)]
                · rw [if_neg (fun h => hmsqf h.1), if_neg hmsqf]
              · rw [if_neg hrd]
                exact (Finset.sum_eq_zero fun m _ => if_neg (fun h => hrd h.1)).symm
          _ = ∑ m ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d ∈ Finset.Icc 1 z,
                if r ∣ d ∧ d ∣ m then (ArithmeticFunction.moebius d : ℝ) * (1 / selbergF g m) else 0 :=
              Finset.sum_comm
          _ = ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ r ∣ m),
                (1 / selbergF g m) *
                  ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius d : ℝ) := by
              rw [Finset.sum_filter, Finset.sum_filter]
              refine Finset.sum_congr rfl fun m _ => ?_
              by_cases hmsqf : Squarefree m
              · by_cases hrm : r ∣ m
                · rw [if_pos hmsqf, if_pos ⟨hmsqf, hrm⟩, Finset.mul_sum, Finset.sum_filter]
                  refine Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
                · rw [if_pos hmsqf, if_neg (fun h => hrm h.2)]
                  exact Finset.sum_eq_zero fun d _ => if_neg (fun h => hrm (h.1.trans h.2))
              · rw [if_neg hmsqf, if_neg (fun h => hmsqf h.1)]
      rw [hswap]
      have hinner : ∀ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ r ∣ m),
          ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius d : ℝ) =
            if m = r then (ArithmeticFunction.moebius r : ℝ) else 0 := by
        intro m hm
        obtain ⟨hmI, hmsqf, hrm⟩ := Finset.mem_filter.mp hm
        have hm_pos : 0 < m := (Finset.mem_Icc.mp hmI).1
        have hm_le : m ≤ z := (Finset.mem_Icc.mp hmI).2
        have hbij :
            ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius d : ℝ) =
            ∑ t ∈ (m / r).divisors, (ArithmeticFunction.moebius (r * t) : ℝ) := by
          symm
          refine Finset.sum_bij (fun t _ => r * t) ?_ ?_ ?_ ?_
          · intro t ht
            obtain ⟨htd, hqne⟩ := Nat.mem_divisors.mp ht
            have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos htd (Nat.pos_of_ne_zero hqne)
            have hrt_dvd : r * t ∣ m := by
              obtain ⟨k, hk⟩ := htd
              exact ⟨k, by rw [← Nat.mul_div_cancel' hrm, hk]; ring⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hr).1 ht_pos,
              (Nat.le_of_dvd hm_pos hrt_dvd).trans hm_le⟩, dvd_mul_right r t, hrt_dvd⟩
          · intro t₁ _ t₂ _ heq
            exact Nat.eq_of_mul_eq_mul_left (Finset.mem_Icc.mp hr).1 heq
          · intro d hd
            obtain ⟨_, hrd, hdm⟩ := Finset.mem_filter.mp hd
            refine ⟨d / r, Nat.mem_divisors.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hrd⟩
            · obtain ⟨k, hk⟩ := hdm
              refine ⟨k, ?_⟩
              have hr_pos : 0 < r := (Finset.mem_Icc.mp hr).1
              have hmul : r * (m / r) = r * ((d / r) * k) := by
                rw [Nat.mul_div_cancel' hrm, ← mul_assoc, Nat.mul_div_cancel' hrd, hk]
              exact Nat.eq_of_mul_eq_mul_left hr_pos hmul
            · intro h0
              have := Nat.mul_div_cancel' hrm
              rw [h0, mul_zero] at this
              omega
          · intro _ _; rfl
        rw [hbij]
        have hcop_rt : ∀ t ∈ (m / r).divisors, Nat.Coprime r t := by
          intro t ht
          have htd : t ∣ m / r := (Nat.mem_divisors.mp ht).1
          have hcop_rq : Nat.Coprime r (m / r) := by
            have hrm_eq : m = r * (m / r) := (Nat.mul_div_cancel' hrm).symm
            exact (Nat.squarefree_mul_iff.mp (hrm_eq ▸ hmsqf)).1
          exact hcop_rq.coprime_dvd_right htd
        have hfact : ∑ t ∈ (m / r).divisors, (ArithmeticFunction.moebius (r * t) : ℝ) =
            (ArithmeticFunction.moebius r : ℝ) * ∑ t ∈ (m / r).divisors, (ArithmeticFunction.moebius t : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t ht => ?_
          have hm_mul : ArithmeticFunction.moebius (r * t) =
              ArithmeticFunction.moebius r * ArithmeticFunction.moebius t :=
            ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hcop_rt t ht)
          exact_mod_cast hm_mul
        rw [hfact]
        by_cases hmr : m = r
        · subst hmr
          rw [if_pos rfl, Nat.div_self (Finset.mem_Icc.mp hr).1]
          simp
        · rw [if_neg hmr]
          have hne1 : m / r ≠ 1 := fun h1 => hmr (by rw [← Nat.mul_div_cancel' hrm, h1, mul_one])
          rw [sum_divisors_moebius_eq_zero_of_ne_one hne1, mul_zero]
      have hcongr :
          ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ r ∣ m),
            (1 / selbergF g m) *
              ∑ d ∈ (Finset.Icc 1 z).filter (fun d => r ∣ d ∧ d ∣ m), (ArithmeticFunction.moebius d : ℝ) =
          ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ r ∣ m),
            (1 / selbergF g m) * (if m = r then (ArithmeticFunction.moebius r : ℝ) else 0) :=
        Finset.sum_congr rfl fun m hm => by rw [hinner m hm]
      rw [hcongr, Finset.sum_eq_single r]
      · rw [if_pos rfl]; field_simp [hGpos.ne', (selbergF_pos hg r).ne']
      · intro m _ hne; rw [if_neg hne, mul_zero]
      · intro hnot; exact absurd (Finset.mem_filter.mpr ⟨hr, hrsqf, dvd_rfl⟩) hnot
    rw [hsum]
    have hfpos := selbergF_pos hg r
    field_simp [hfpos.ne', hGpos.ne']
  · rw [moebius_eq_zero_of_not_squarefree hrsqf]
    simp

/-- **Exact Optimal Selberg Sieve Bound**: `Q(λ*) = 1 / G(z)`. -/
theorem selberg_optLam_eq_min {z : ℕ} (hz : 1 ≤ z) {g : ℕ → ℝ} (hg : IsSelbergDensity g) :
    selbergQuadForm z g (selbergOptLam z g) = 1 / selbergG g z := by
  rw [selberg_completing_square hz hg (selbergOptLam_eq_zero_of_not_squarefree z g) (selbergOptLam_one hz hg)]
  have hzero : ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
      (selbergY z g (selbergOptLam z g) r - 1 / selbergG g z) ^ 2 / selbergF g r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    obtain ⟨hrI, hrsqf⟩ := Finset.mem_filter.mp hr
    rw [selbergY_optLam hz hg hrI, moebius_sq_eq_one_of_squarefree hrsqf, sub_self, zero_pow (by norm_num), zero_div]
  rw [hzero, add_zero]

/-- **Möbius Inversion Recovery**: if two squarefree-supported weight functions have identical
`selbergY` on `Icc 1 z`, they agree identically on `Icc 1 z`. -/
theorem selberg_eq_of_selbergY_eq {z : ℕ} {g lam₁ lam₂ : ℕ → ℝ} (hg : IsSelbergDensity g)
    (hsupp₁ : ∀ d, ¬ Squarefree d → lam₁ d = 0)
    (hsupp₂ : ∀ d, ¬ Squarefree d → lam₂ d = 0)
    (hY : ∀ r ∈ Finset.Icc 1 z, selbergY z g lam₁ r = selbergY z g lam₂ r) :
    ∀ d ∈ Finset.Icc 1 z, lam₁ d = lam₂ d := by
  intro d hd
  by_cases hdsqf : Squarefree d
  · -- Prove by strong induction on `z - d` (downward on `d ≤ z`)
    induction hdiff : z - d using Nat.strong_induction_on generalizing d with
    | _ k ih =>
      have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hd_le : d ≤ z := (Finset.mem_Icc.mp hd).2
      have hYd := hY d hd
      unfold selbergY at hYd
      have hmu_ne : (ArithmeticFunction.moebius d : ℝ) ≠ 0 := by
        intro h0
        have hsq := moebius_sq_eq_one_of_squarefree hdsqf
        rw [h0, zero_pow (by norm_num)] at hsq
        norm_num at hsq
      have hf_ne : selbergF g d ≠ 0 := (selbergF_pos hg d).ne'
      have hS_eq :
          ∑ e ∈ (Finset.Icc 1 z).filter (fun e => d ∣ e), lam₁ e * g e =
          ∑ e ∈ (Finset.Icc 1 z).filter (fun e => d ∣ e), lam₂ e * g e :=
        mul_left_cancel₀ (mul_ne_zero hmu_ne hf_ne) hYd
      have hd_mem : d ∈ (Finset.Icc 1 z).filter (fun e => d ∣ e) :=
        Finset.mem_filter.mpr ⟨hd, dvd_rfl⟩
      rw [← Finset.add_sum_erase _ _ hd_mem, ← Finset.add_sum_erase _ _ hd_mem] at hS_eq
      have hrest :
          ∑ e ∈ ((Finset.Icc 1 z).filter (fun e => d ∣ e)).erase d, lam₁ e * g e =
          ∑ e ∈ ((Finset.Icc 1 z).filter (fun e => d ∣ e)).erase d, lam₂ e * g e := by
        refine Finset.sum_congr rfl fun e he => ?_
        obtain ⟨hne, hefilt⟩ := Finset.mem_erase.mp he
        obtain ⟨heI, hde⟩ := Finset.mem_filter.mp hefilt
        by_cases hesqf : Squarefree e
        · have he_gt : d < e := lt_of_le_of_ne (Nat.le_of_dvd (Finset.mem_Icc.mp heI).1 hde) (Ne.symm hne)
          have he_le : e ≤ z := (Finset.mem_Icc.mp heI).2
          have hlt : z - e < k := by omega
          rw [ih (z - e) hlt e heI hesqf rfl]
        · rw [hsupp₁ e hesqf, hsupp₂ e hesqf]
      have hgd_ne : g d ≠ 0 := (selberg_density_pos_of_pos hg hd_pos).ne'
      have hmul : lam₁ d * g d = lam₂ d * g d := by linarith
      exact mul_right_cancel₀ hgd_ne hmul
  · rw [hsupp₁ d hdsqf, hsupp₂ d hdsqf]

/-- **Uniqueness of the Optimal Selberg Sieve Minimizer**:
among squarefree-supported weights `λ` with `λ_1 = 1`, `Q(λ) = 1 / G(z)` if and only if
`λ d = λ*_d` for all `d ∈ Finset.Icc 1 z`. -/
theorem selberg_optLam_unique {z : ℕ} (hz : 1 ≤ z) {g lam : ℕ → ℝ} (hg : IsSelbergDensity g)
    (hsupp : ∀ d, ¬ Squarefree d → lam d = 0) (hlam1 : lam 1 = 1) :
    selbergQuadForm z g lam = 1 / selbergG g z ↔
      ∀ d ∈ Finset.Icc 1 z, lam d = selbergOptLam z g d := by
  constructor
  · intro heq
    rw [selberg_completing_square hz hg hsupp hlam1] at heq
    have hsum0 : ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
        (selbergY z g lam r - 1 / selbergG g z) ^ 2 / selbergF g r = 0 := by linarith
    have hY_eq : ∀ r ∈ Finset.Icc 1 z, selbergY z g lam r = selbergY z g (selbergOptLam z g) r := by
      intro r hr
      by_cases hrsqf : Squarefree r
      · have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
          div_nonneg (sq_nonneg _) (selbergF_pos hg s).le)).mp hsum0 r
          (Finset.mem_filter.mpr ⟨hr, hrsqf⟩)
        have hsq0 : (selbergY z g lam r - 1 / selbergG g z) ^ 2 = 0 :=
          (div_eq_zero_iff.mp hterm).resolve_right (selbergF_pos hg r).ne'
        have hy : selbergY z g lam r = 1 / selbergG g z := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
        rw [hy, selbergY_optLam hz hg hr, moebius_sq_eq_one_of_squarefree hrsqf]
      · unfold selbergY
        rw [moebius_eq_zero_of_not_squarefree hrsqf]
        simp
    exact selberg_eq_of_selbergY_eq hg hsupp (selbergOptLam_eq_zero_of_not_squarefree z g) hY_eq
  · intro hall
    have hq_eq : selbergQuadForm z g lam = selbergQuadForm z g (selbergOptLam z g) := by
      unfold selbergQuadForm
      refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
      rw [hall d₁ hd₁, hall d₂ hd₂]
    rw [hq_eq, selberg_optLam_eq_min hz hg]

/-- **Classic Selberg Weight Bound**: `|λ*_d| ≤ 1` for EVERY `d : ℕ`! -/
theorem abs_selbergOptLam_le_one {z : ℕ} (hz : 1 ≤ z) {g : ℕ → ℝ} (hg : IsSelbergDensity g) (d : ℕ) :
    |selbergOptLam z g d| ≤ 1 := by
  by_cases hdI : d ∈ Finset.Icc 1 z
  · by_cases hdsqf : Squarefree d
    · have hGpos : 0 < selbergG g z := lt_of_lt_of_le zero_lt_one (one_le_selbergG hg hz)
      have hd_pos : 0 < d := (Finset.mem_Icc.mp hdI).1
      have hgd_pos : 0 < g d := selberg_density_pos_of_pos hg hd_pos
      have hfd_pos : 0 < selbergF g d := selbergF_pos hg d
      -- Step 1: `∑_{e ∣ d} 1 / f(e) = 1 / (g(d) * f(d))`
      have hsum_e : ∑ e ∈ d.divisors, 1 / selbergF g e = 1 / (g d * selbergF g d) := by
        have h1 : 1 / (g d * selbergF g d) = ∏ p ∈ d.primeFactors, (1 + 1 / (1 / g p - 1)) := by
          rw [selberg_density_eq_prod_of_squarefree hg hdsqf]
          unfold selbergF
          rw [← Finset.prod_mul_distrib, one_div, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun p hp => ?_
          obtain ⟨h0, h1⟩ := hg.2.2 p (Nat.prime_of_mem_primeFactors hp)
          field_simp [h0.ne', (by linarith : 1 - g p ≠ 0)]
          ring
        rw [h1, Finset.prod_one_add]
        symm
        refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
        · intro S hS
          have hsub := Finset.mem_powerset.mp hS
          exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset S d.primeFactors id hsub).trans
            (Nat.prod_primeFactors_dvd d), hd_pos.ne'⟩
        · intro S₁ hS₁ S₂ hS₂ heq
          have hsub₁ := Finset.mem_powerset.mp hS₁
          have hsub₂ := Finset.mem_powerset.mp hS₂
          have hpf : ∀ S ⊆ d.primeFactors, (∏ p ∈ S, p).primeFactors = S := by
            intro S hsub
            ext r; simp only [Nat.mem_primeFactors]
            constructor
            · rintro ⟨hr, hdvd, -⟩
              obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
              rwa [(Nat.prime_dvd_prime_iff_eq hr (Nat.prime_of_mem_primeFactors (hsub hp))).mp hrp]
            · intro hr
              exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr,
                (squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero⟩
          rw [← hpf S₁ hsub₁, ← hpf S₂ hsub₂, heq]
        · intro e he
          obtain ⟨hed, -⟩ := Nat.mem_divisors.mp he
          exact ⟨e.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hed hd_pos.ne'),
            Nat.prod_primeFactors_of_squarefree (hdsqf.squarefree_of_dvd hed)⟩
        · intro S hS
          have hsub := Finset.mem_powerset.mp hS
          have hpf : (∏ p ∈ S, p).primeFactors = S := by
            ext r; simp only [Nat.mem_primeFactors]
            constructor
            · rintro ⟨hr, hdvd, -⟩
              obtain ⟨p, hp, hrp⟩ := hr.prime.dvd_finsetProd_iff _ |>.mp hdvd
              rwa [(Nat.prime_dvd_prime_iff_eq hr (Nat.prime_of_mem_primeFactors (hsub hp))).mp hrp]
            · intro hr
              exact ⟨Nat.prime_of_mem_primeFactors (hsub hr), Finset.dvd_prod_of_mem _ hr,
                (squarefree_prod_primeFactors S fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero⟩
          unfold selbergF
          rw [hpf, one_div, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun _ _ => one_div _
      -- Step 2: rewrite `∑_{m ≤ z, sqf, d ∣ m} 1 / f(m) = (1 / f(d)) * ∑_{k ≤ z/d, sqf, (k,d)=1} 1 / f(k)`
      set K : Finset ℕ := (Finset.Icc 1 (z / d)).filter (fun k => Squarefree k ∧ Nat.Coprime k d)
      have hsum_m :
          ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Squarefree m ∧ d ∣ m), 1 / selbergF g m =
          (1 / selbergF g d) * ∑ k ∈ K, 1 / selbergF g k := by
        rw [Finset.mul_sum]
        symm
        refine Finset.sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
        · intro k hk
          obtain ⟨hkI, hksqf, hkcop⟩ := Finset.mem_filter.mp hk
          obtain ⟨hk1, hkzd⟩ := Finset.mem_Icc.mp hkI
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd_pos hk1,
            (Nat.mul_le_mul_left d hkzd).trans (Nat.mul_div_le z d)⟩,
            (Nat.squarefree_mul hkcop.symm).mpr ⟨hdsqf, hksqf⟩, dvd_mul_right d k⟩
        · intro k₁ _ k₂ _ heq
          exact Nat.eq_of_mul_eq_mul_left hd_pos heq
        · intro m hm
          obtain ⟨hmI, hmsqf, hdm⟩ := Finset.mem_filter.mp hm
          obtain ⟨hm1, hmz⟩ := Finset.mem_Icc.mp hmI
          set k : ℕ := m / d
          have hdk : d * k = m := Nat.mul_div_cancel' hdm
          have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hdk; omega
          have hkzd : k ≤ z / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hdk]; exact hmz)
          have hpair := Nat.squarefree_mul_iff.mp (hdk.symm ▸ hmsqf)
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkzd⟩, hpair.2.2, hpair.1.symm⟩, hdk⟩
        · intro k hk
          obtain ⟨_, _, hkcop⟩ := Finset.mem_filter.mp hk
          rw [selbergF_mul_coprime g hkcop.symm]
          ring
      -- Step 3: inject `d.divisors ×ˢ K` into `(Icc 1 z).filter Squarefree` via `(e, k) ↦ e * k`
      have hprod_le : (∑ e ∈ d.divisors, 1 / selbergF g e) * (∑ k ∈ K, 1 / selbergF g k) ≤
          selbergG g z := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        unfold selbergG
        have hmaps : ∀ ek ∈ d.divisors ×ˢ K, ek.1 * ek.2 ∈ (Finset.Icc 1 z).filter Squarefree := by
          intro ek hek
          obtain ⟨he, hk⟩ := Finset.mem_product.mp hek
          obtain ⟨hed, -⟩ := Nat.mem_divisors.mp he
          obtain ⟨hkI, hksqf, hkcop⟩ := Finset.mem_filter.mp hk
          obtain ⟨hk1, hkzd⟩ := Finset.mem_Icc.mp hkI
          have he_pos : 0 < ek.1 := Nat.pos_of_dvd_of_pos hed hd_pos
          have he_le : ek.1 ≤ d := Nat.le_of_dvd hd_pos hed
          have he_sqf : Squarefree ek.1 := hdsqf.squarefree_of_dvd hed
          have hek_cop : Nat.Coprime ek.1 ek.2 := (hkcop.coprime_dvd_right hed).symm
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos he_pos hk1,
            (Nat.mul_le_mul he_le hkzd).trans (Nat.mul_div_le z d)⟩,
            (Nat.squarefree_mul hek_cop).mpr ⟨he_sqf, hksqf⟩⟩
        have hinj : Set.InjOn (fun ek : ℕ × ℕ => ek.1 * ek.2) ((d.divisors ×ˢ K : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
          intro ek₁ h₁ ek₂ h₂ heq
          dsimp only at heq
          obtain ⟨he₁, hk₁⟩ := Finset.mem_product.mp h₁
          obtain ⟨he₂, hk₂⟩ := Finset.mem_product.mp h₂
          have hed₁ : ek₁.1 ∣ d := (Nat.mem_divisors.mp he₁).1
          have hed₂ : ek₂.1 ∣ d := (Nat.mem_divisors.mp he₂).1
          have hkcop₁ : Nat.Coprime ek₁.2 d := (Finset.mem_filter.mp hk₁).2.2
          have hkcop₂ : Nat.Coprime ek₂.2 d := (Finset.mem_filter.mp hk₂).2.2
          have hdvd12 : ek₁.1 ∣ ek₂.1 :=
            ((hkcop₂.coprime_dvd_right hed₁).symm).dvd_of_dvd_mul_right (heq ▸ dvd_mul_right ek₁.1 ek₁.2)
          have hdvd21 : ek₂.1 ∣ ek₁.1 :=
            ((hkcop₁.coprime_dvd_right hed₂).symm).dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right ek₂.1 ek₂.2)
          have he_eq : ek₁.1 = ek₂.1 := Nat.dvd_antisymm hdvd12 hdvd21
          have he_pos : 0 < ek₁.1 := Nat.pos_of_dvd_of_pos hed₁ hd_pos
          have hk_eq : ek₁.2 = ek₂.2 :=
            Nat.eq_of_mul_eq_mul_left he_pos (by rw [he_eq] at heq ⊢; exact heq)
          exact Prod.ext he_eq hk_eq
        have hterm : ∀ ek ∈ d.divisors ×ˢ K,
            (1 / selbergF g ek.1) * (1 / selbergF g ek.2) = 1 / selbergF g (ek.1 * ek.2) := by
          intro ek hek
          obtain ⟨he, hk⟩ := Finset.mem_product.mp hek
          have hed : ek.1 ∣ d := (Nat.mem_divisors.mp he).1
          have hkcop : Nat.Coprime ek.2 d := (Finset.mem_filter.mp hk).2.2
          rw [selbergF_mul_coprime g (hkcop.coprime_dvd_right hed).symm]
          ring
        calc ∑ ek ∈ d.divisors ×ˢ K, (1 / selbergF g ek.1) * (1 / selbergF g ek.2)
            = ∑ ek ∈ d.divisors ×ˢ K, 1 / selbergF g (ek.1 * ek.2) :=
              Finset.sum_congr rfl hterm
          _ = ∑ m ∈ (d.divisors ×ˢ K).image (fun ek => ek.1 * ek.2), 1 / selbergF g m :=
              (Finset.sum_image (f := fun m => 1 / selbergF g m) hinj).symm
          _ ≤ ∑ m ∈ (Finset.Icc 1 z).filter Squarefree, 1 / selbergF g m :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
                fun r _ _ => div_nonneg zero_le_one (selbergF_pos hg r).le
      rw [hsum_e] at hprod_le
      -- Conclude `|selbergOptLam z g d| ≤ 1`
      unfold selbergOptLam
      rw [if_pos hdI, hsum_m, abs_mul, abs_div, abs_mul, abs_of_pos hgd_pos, abs_of_pos hGpos]
      have habs_mu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
        have hsq := moebius_sq_eq_one_of_squarefree hdsqf
        have h1 : |(ArithmeticFunction.moebius d : ℝ)| ^ 2 = 1 := by rw [sq_abs, hsq]
        nlinarith [abs_nonneg (ArithmeticFunction.moebius d : ℝ)]
      have hK_nn : 0 ≤ ∑ k ∈ K, 1 / selbergF g k :=
        Finset.sum_nonneg fun k _ => div_nonneg zero_le_one (selbergF_pos hg k).le
      rw [habs_mu, abs_of_nonneg (mul_nonneg (div_nonneg zero_le_one hfd_pos.le) hK_nn)]
      have hlhs : 1 / (g d * selbergG g z) * (1 / selbergF g d * ∑ k ∈ K, 1 / selbergF g k) =
          (1 / (g d * selbergF g d) * ∑ k ∈ K, 1 / selbergF g k) / selbergG g z := by
        field_simp [hgd_pos.ne', hfd_pos.ne', hGpos.ne']
      rw [hlhs, div_le_one hGpos]
      exact hprod_le
    · rw [selbergOptLam_eq_zero_of_not_squarefree z g d hdsqf, abs_zero]; exact zero_le_one
  · unfold selbergOptLam; rw [if_neg hdI, abs_zero]; exact zero_le_one

/-- **Selberg Upper-Bound Sieve for Finite Sets**:
for any finite `A : Finset ℕ`, `1 ≤ z`, completely multiplicative Selberg density `g`,
main-term scale `X : ℝ`, and remainder function `R : ℕ → ℝ` with
`|(A.filter (d ∣ ·))| = X * g(d) + R(d)` for all squarefree `d`,
`#{n ∈ A : n > 0 ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n} ≤ X / G(z) + ∑_{d₁, d₂ ≤ z, sqf} |R([d₁, d₂])|`. -/
theorem selberg_upper_bound_sieve (A : Finset ℕ) {z : ℕ} (hz : 1 ≤ z)
    {g : ℕ → ℝ} (hg : IsSelbergDensity g) (X : ℝ) (R : ℕ → ℝ)
    (hModel : ∀ d : ℕ, Squarefree d → ((A.filter (fun n => d ∣ n)).card : ℝ) = X * g d + R d) :
    ((A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n)).card : ℝ) ≤
      X / selbergG g z +
        ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree,
          ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree, |R (Nat.lcm d₁ d₂)| := by
  let lam := selbergOptLam z g
  have hlam1 : lam 1 = 1 := selbergOptLam_one hz hg
  have hsupp : ∀ d, ¬ Squarefree d → lam d = 0 := selbergOptLam_eq_zero_of_not_squarefree z g
  -- Step 1: Indicator bound `1_{sifted}(n) ≤ (∑_{d ≤ z, d ∣ n} λ_d)²`
  have hind :
      ((A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n)).card : ℝ) ≤
        ∑ n ∈ A, (∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n), lam d) ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hn : 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n
    · rw [if_pos hn, Nat.cast_one]
      have hfilt : (Finset.Icc 1 z).filter (fun d => d ∣ n) = {1} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hd1, hdz⟩, hdn⟩
          by_contra hdne1
          obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hdne1
          have hpz : p ≤ z := (Nat.le_of_dvd (by omega) hpd).trans hdz
          exact hn.2 p hpz hp (hpd.trans hdn)
        · rintro rfl; exact ⟨⟨le_rfl, hz⟩, one_dvd n⟩
      rw [hfilt, Finset.sum_singleton, hlam1, one_pow]
    · rw [if_neg hn]
      exact sq_nonneg _
  -- Step 2: Expand the square and swap sums
  have hexp :
      ∑ n ∈ A, (∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n), lam d) ^ 2 =
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * ((A.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) := by
    calc ∑ n ∈ A, (∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n), lam d) ^ 2
        = ∑ n ∈ A, ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
            if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [sq, Finset.sum_mul, Finset.sum_filter]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          by_cases h1 : d₁ ∣ n
          · rw [if_pos h1, Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d₂ _ => by by_cases h2 : d₂ ∣ n <;> simp [h1, h2]
          · rw [if_neg h1]
            exact (Finset.sum_eq_zero fun d₂ _ => if_neg (fun h => h1 h.1)).symm
      _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ n ∈ A, ∑ d₂ ∈ Finset.Icc 1 z,
            if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 := Finset.sum_comm
      _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z, ∑ n ∈ A,
            if d₁ ∣ n ∧ d₂ ∣ n then lam d₁ * lam d₂ else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
            lam d₁ * lam d₂ * ((A.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
          have hcond : ∀ n : ℕ, (d₁ ∣ n ∧ d₂ ∣ n) ↔ Nat.lcm d₁ d₂ ∣ n :=
            fun _ => Nat.lcm_dvd_iff.symm
          simp_rw [hcond, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 3: Substitute the sieve model `X * g([d₁, d₂]) + R([d₁, d₂])`
  have hsub :
      ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
          lam d₁ * lam d₂ * ((A.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) =
        X * selbergQuadForm z g lam +
          ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
            lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂) := by
    have hsplit_inner :
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
            lam d₁ * lam d₂ * ((A.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) =
        ∑ d₁ ∈ Finset.Icc 1 z, ∑ d₂ ∈ Finset.Icc 1 z,
            (X * (lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)) +
              (if Squarefree d₁ ∧ Squarefree d₂ then lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂) else 0)) := by
      refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
      by_cases h1 : Squarefree d₁
      · by_cases h2 : Squarefree d₂
        · have hlcm_sqf : Squarefree (Nat.lcm d₁ d₂) := by
            rw [Nat.squarefree_iff_prime_squarefree]
            intro p hp hpsq
            have hpd : p * p ∣ d₁ ∨ p * p ∣ d₂ := by
              have hne : Nat.lcm d₁ d₂ ≠ 0 := Nat.lcm_ne_zero h1.ne_zero h2.ne_zero
              have hfac : 2 ≤ (Nat.lcm d₁ d₂).factorization p := by
                have hpow : p ^ 2 ∣ Nat.lcm d₁ d₂ := by rwa [sq]
                exact (hp.pow_dvd_iff_le_factorization hne).mp hpow
              rw [Nat.factorization_lcm h1.ne_zero h2.ne_zero, Finsupp.sup_apply] at hfac
              rcases le_max_iff.mp hfac with h | h
              · left; rw [← sq]; exact (hp.pow_dvd_iff_le_factorization h1.ne_zero).mpr h
              · right; rw [← sq]; exact (hp.pow_dvd_iff_le_factorization h2.ne_zero).mpr h
            rcases hpd with h | h
            · exact hp.ne_one (Nat.isUnit_iff.mp (h1 p h))
            · exact hp.ne_one (Nat.isUnit_iff.mp (h2 p h))
          rw [hModel (Nat.lcm d₁ d₂) hlcm_sqf, if_pos ⟨h1, h2⟩]; ring
        · rw [hsupp d₂ h2, if_neg (fun h => h2 h.2)]; ring
      · rw [hsupp d₁ h1, if_neg (fun h => h1 h.1)]; ring
    rw [hsplit_inner]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · unfold selbergQuadForm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => (Finset.mul_sum _ _ _).symm
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      by_cases h1 : Squarefree d₁
      · rw [if_pos h1, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d₂ _ => by by_cases h2 : Squarefree d₂ <;> simp [h1, h2]
      · rw [if_neg h1]
        exact Finset.sum_eq_zero fun d₂ _ => if_neg (fun h => h1 h.1)
  -- Step 4: Evaluate `Q(λ*) = 1 / G(z)` and bound remainder using `|λ*_d| ≤ 1`
  have hrem :
      ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
          lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂) ≤
      ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
          |R (Nat.lcm d₁ d₂)| := by
    refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
    calc lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂)
        ≤ |lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂)| := le_abs_self _
      _ = |lam d₁| * |lam d₂| * |R (Nat.lcm d₁ d₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |R (Nat.lcm d₁ d₂)| := by
          have h1 := abs_selbergOptLam_le_one hz hg d₁
          have h2 := abs_selbergOptLam_le_one hz hg d₂
          have hmul : |lam d₁| * |lam d₂| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
      _ = |R (Nat.lcm d₁ d₂)| := by ring
  calc ((A.filter (fun n => 0 < n ∧ ∀ p ≤ z, p.Prime → ¬ p ∣ n)).card : ℝ)
      ≤ ∑ n ∈ A, (∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n), lam d) ^ 2 := hind
    _ = X * selbergQuadForm z g lam +
          ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
            lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂) := by rw [hexp, hsub]
    _ = X / selbergG g z +
          ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
            lam d₁ * lam d₂ * R (Nat.lcm d₁ d₂) := by
          rw [selberg_optLam_eq_min hz hg, mul_one_div]
    _ ≤ X / selbergG g z +
          ∑ d₁ ∈ (Finset.Icc 1 z).filter Squarefree, ∑ d₂ ∈ (Finset.Icc 1 z).filter Squarefree,
            |R (Nat.lcm d₁ d₂)| := by linarith

end Stage7SieveMethods
end RHDirect

end
