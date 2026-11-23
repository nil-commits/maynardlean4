/-
MaynardDock — Unconditional Polymath8b Capstone (H = 246).

Composes Wave 1 (`MaynardDock.maynardBombieriVinogradov`, derived unconditionally from
`RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov`) with AxiomMath's
`PrimeGaps.Bounded246` (enlarged Maynard–Tao sieve + kernel-checked certificate
`PrimeGaps.existsEpsCert50` for `M_{50, 1/25} > 4`) to obtain unconditional
bounded prime gaps with explicit bound `H = 246` and 0 parameters.
-/
import MaynardDock.BombieriVinogradovAdapter
import PrimeGaps.Bounded246

namespace MaynardDock

/-- **Unconditional Polymath8b bounded prime gaps (explicit bound `H = 246`)**:
for every `N`, there exist primes `p, q` with `N < p < q` and `q - p ≤ 246`. -/
theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246 := by
  intro N
  obtain ⟨p, q, hpN, hpq, hp, hq, hgap⟩ :=
    bombieriVinogradov_implies_prime_gap_le_246 maynardBombieriVinogradov (N + 1)
  exact ⟨p, q, by omega, hpq, hp, hq, by omega⟩

/-- **Unconditional Bounded Prime Gaps with `H = 246` (0 parameters)**. -/
theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  ⟨246, by norm_num, le_rfl, unconditional_prime_gap_le_246⟩

/-- **Unconditional consecutive prime gaps ≤ 246 infinitely often**
(`Nat.nth Nat.Prime` formulation). -/
theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop :=
  bombieriVinogradov_implies_frequently_prime_gap_le_246 maynardBombieriVinogradov

/-- **Unconditional `nth`-prime gap bound `p_{n+1} ≤ p_n + 246` for arbitrarily large `n`**. -/
theorem unconditional_nth_prime_gap_le_246 :
    ∀ n₀ : ℕ, ∃ n ≥ n₀, Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime n + 246 :=
  bombieriVinogradov_implies_nth_prime_gap_le_246 maynardBombieriVinogradov

end MaynardDock
