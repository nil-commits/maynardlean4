# maynardlean4 — Unconditional Bounded Prime Gaps ($H = 600$) in Lean 4

An **unconditional, zero-parameter, Lean 4 kernel-verified** proof of Maynard–Tao's Bounded Prime Gaps theorem ($H = 600$):

```lean
theorem MaynardDock.bounded_prime_gaps_unconditional :
    ∃ H : ℕ, 0 < H ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H

theorem MaynardDock.unconditional_prime_gap_le_600 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 600

theorem MaynardDock.frequently_consecutive_prime_gap_le_600 :
    Filter.Frequently
      (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 600)
      Filter.atTop
```

All theorems are verified with **0 `sorry`**, **0 custom `axiom`**, **0 `opaque`**, **0 `native_decide`**, and pass both `lake env leanchecker MaynardDock.Capstone` and `#print axioms`:

```text
'MaynardDock.maynardBombieriVinogradov' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaynardDock.unconditional_prime_gap_le_600' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaynardDock.bounded_prime_gaps_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'MaynardDock.frequently_consecutive_prime_gap_le_600' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Architecture

This project docks the **unconditional Bombieri–Vinogradov theorem** from [`nil-commits/alpoge-rh-golf`](https://github.com/nil-commits/alpoge-rh-golf) (`rh-direct-v1.2.0`) onto the **Maynard–Tao sieve and variational machinery** from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) (vendored unmodified under Apache-2.0), discharging its `BombieriVinogradov` hypothesis completely:

```text
RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov   (unconditional ψ-form, θ < 1/2)
        │
        ▼  MaynardDock/BombieriVinogradovAdapter.lean    (exact Abel summation + level geometry)
PrimeGapsTheory.NumberTheory.BombieriVinogradov.BombieriVinogradov   (π-form, θ < 1/2)
        │
        ▼  PrimeGapsTheory.Endgame.Main                  (vendored AxiomMath/PrimeGapsLib, M₁₀₅ > 4)
bombieriVinogradov_implies_prime_gap_le_600
        │
        ▼  MaynardDock/Capstone.lean                     (0-parameter unconditional capstone)
MaynardDock.bounded_prime_gaps_unconditional  (H = 600)
```

### Our Modules (`MaynardDock/`)

| Module | Role |
| :--- | :--- |
| `MaynardDock/BombieriVinogradovAdapter.lean` | Bridges `RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov` ($\psi$-form) to `BombieriVinogradov` ($\pi$-form) for all $\theta < 1/2$ and $A \ge 1$ via exact Abel summation, uniform prime-power gap bounds, $\sum\int$-commutation, level split at $T = x^{(1+2\theta)/2}$, and harmonic/totient reciprocal sum bounds. |
| `MaynardDock/Capstone.lean` | Zero-parameter unconditional theorems: `unconditional_prime_gap_le_600`, `bounded_prime_gaps_unconditional`, `frequently_consecutive_prime_gap_le_600`. |
| `MaynardDock/Audit.lean` | `#print axioms` census across all top-level `MaynardDock` theorems. |
| `MaynardDock.lean` | Umbrella root module. |

## Build & Verify

Toolchain: `leanprover/lean4:v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

1. Clone [`nil-commits/alpoge-rh-golf`](https://github.com/nil-commits/alpoge-rh-golf) (branch `rh-direct`, tag `rh-direct-v1.2.0`) alongside this repository at `../alpoge-rh-golf` and apply the Lake 5 build-config patch (`patches/alpoge-rh-golf-lake5.patch`, plus an umbrella `RHDirect.lean` if running `lake build` there).
2. Fetch dependencies (`lake update` / `lake exe cache get`) and apply the 1-line Mathlib-compatibility patch `patches/PrimeNumberTheoremAnd-MediumPNT.patch` inside `.lake/packages/PrimeNumberTheoremAnd`.
3. Build and verify:

```sh
lake build MaynardDock MaynardDock.Audit
lake env lean MaynardDock/Audit.lean
lake env leanchecker MaynardDock.Capstone
```

## Third-Party Attribution & License

- Repository license: **Apache-2.0** (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
- `PrimeGapsTheory/` and `PrimeGapsCert/` are vendored unmodified from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) (Copyright 2026 Axiom Math, Apache-2.0).
- `PrimeNumberTheoremAnd` is pinned at `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed` (AxiomMath fork) with a 1-line compatibility patch in `patches/PrimeNumberTheoremAnd-MediumPNT.patch`.
- Unconditional Bombieri–Vinogradov is imported from [`nil-commits/alpoge-rh-golf`](https://github.com/nil-commits/alpoge-rh-golf) (`rh-direct-v1.2.0`).
