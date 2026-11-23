import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Unconditional Bounded Prime Gaps (H = 246) — Trustless Challenge Specification

This file imports **only upstream Mathlib** and introduces **zero custom definitions**.
Every symbol (`Nat.Prime`, `Nat.nth`, `Filter.Frequently`, `Filter.atTop`) is from Mathlib.

To verify `Solution.lean` against this file without trusting any intermediate module,
check that each theorem below is proved in `Solution.lean` with identical type using only
the standard Lean axioms `{propext, Classical.choice, Quot.sound}`.
-/

/-- For every `N`, there exist primes `N < p < q` with `q - p ≤ 246`. -/
theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246 :=
  sorry

/-- There exists `0 < H ≤ 246` such that arbitrarily large prime pairs differ by at most `H`. -/
theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  sorry

/-- Consecutive prime gaps are at most `246` infinitely often (`Nat.nth Nat.Prime` form). -/
theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop :=
  sorry
