/-
MaynardDock — Wave 3 Capstone.

Composes Wave 1 (`MaynardDock.maynardBombieriVinogradov`, derived unconditionally from
`RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov`) with Wave 2
(`PrimeGapsTheory.Endgame.Main`, Maynard–Tao sieve + variational bound `M 105 > 4`)
to obtain unconditional Bounded Prime Gaps with 0 parameters.
-/
import MaynardDock.BombieriVinogradovAdapter
import PrimeGapsTheory.Endgame.Main

namespace MaynardDock

/-- **Unconditional Maynard–Tao bounded prime gaps (explicit bound `H = 600`)**:
for every `N`, there exist primes `p, q` with `N < p < q` and `q - p ≤ 600`. -/
theorem unconditional_prime_gap_le_600 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 600 := by
  intro N
  obtain ⟨p, q, hpN, hpq, hp, hq, hgap⟩ :=
    bombieriVinogradov_implies_prime_gap_le_600 maynardBombieriVinogradov (N + 1)
  exact ⟨p, q, by omega, hpq, hp, hq, by omega⟩

/-- **Unconditional Bounded Prime Gaps (Capstone, 0 parameters)**:
there exists `H > 0` such that for every `N`, there exist primes `N < p < q`
with `q - p ≤ H`. -/
theorem bounded_prime_gaps_unconditional :
    ∃ H : ℕ, 0 < H ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  ⟨600, by norm_num, unconditional_prime_gap_le_600⟩

/-- **Unconditional consecutive prime gaps ≤ 600 infinitely often**
(`Nat.nth Nat.Prime` formulation). -/
theorem frequently_consecutive_prime_gap_le_600 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 600)
      Filter.atTop :=
  PrimeGaps.thm_main maynardBombieriVinogradov

end MaynardDock
