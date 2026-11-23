import MaynardDock.Capstone246

/-!
# Unconditional Bounded Prime Gaps (H = 246) — Solution

Discharges all three theorems declared in `Challenge.lean` unconditionally with 0 parameters.
-/

theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246 :=
  MaynardDock.unconditional_prime_gap_le_246

theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  MaynardDock.bounded_prime_gaps_246_unconditional

theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop :=
  MaynardDock.frequently_consecutive_prime_gap_le_246
