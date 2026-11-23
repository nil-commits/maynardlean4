# maynardlean4 — Unconditional Bounded Prime Gaps  ($H = 246$) in Lean 4

[![Trustless Verification CI](https://github.com/nil-commits/maynardlean4/actions/workflows/ci.yml/badge.svg)](https://github.com/nil-commits/maynardlean4/actions/workflows/ci.yml)

A **self-contained, unconditional, zero-parameter** Lean 4 proof of Polymath8b / Maynard–Tao's Bounded Prime Gaps theorem ($H = 246$), verified by **two independent type checkers**: the official Lean 4 kernel (`leanchecker --fresh`) and the independent Rust kernel [`nanoda`](https://github.com/ammkrn/nanoda_lib) (89,600 transitive declarations checked, 0 errors).

## Trustless Statement (`Challenge.lean`)

[`Challenge.lean`](Challenge.lean) imports **only upstream Mathlib** (`Mathlib.Data.Nat.Prime.Nth` and `Mathlib.Order.Filter.AtTopBot.Defs`) and introduces **zero custom definitions**:

```lean
theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246

theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H

theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently
      (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop
```

[`Solution.lean`](Solution.lean) proves all three theorems with **0 `sorry`**, **0 custom `axiom`**, **0 `opaque`**, and **0 `native_decide`**, depending solely on the three standard Lean axioms:

```text
OK unconditional_prime_gap_le_246: exact type match, axioms = [propext, Classical.choice, Quot.sound]
OK bounded_prime_gaps_246_unconditional: exact type match, axioms = [propext, Classical.choice, Quot.sound]
OK frequently_consecutive_prime_gap_le_246: exact type match, axioms = [propext, Classical.choice, Quot.sound]
```

## Architecture

This repository is **100% self-contained** with only public GitHub dependencies (`leanprover-community/mathlib4` and a public `v4.33.1`-compatible fork of `AxiomMath/PrimeNumberTheoremAnd`):

```text
RHDirect/ (38-module self-contained analytic NT slice: unconditional Bombieri–Vinogradov, ψ-form)
        │
        ▼  MaynardDock/BombieriVinogradovAdapter.lean    (exact Abel summation + level geometry)
PrimeGapsTheory.NumberTheory.BombieriVinogradov.BombieriVinogradov   (π-form, θ < 1/2)
        │
        ├──► PrimeGapsTheory.Endgame.Main        (M₁₀₅ > 4)      ──► MaynardDock/Capstone.lean    (H = 600)
        │
        └──► PrimeGaps.Bounded246                (M₅₀,₁/₂₅ > 4,  ──► MaynardDock/Capstone246.lean (H = 246)
             + PrimeGapsCert.Gap246.Witness       decide +kernel)        ──► Solution.lean
```

### Repository Layout

| Path | Role |
| :--- | :--- |
| `Challenge.lean` | Minimal human-auditable specification (2 Mathlib imports, 0 custom defs, 3 theorems with `sorry`). |
| `Solution.lean` | Proves all 3 theorems in `Challenge.lean` unconditionally. |
| `Comparator/comparator.json` | Configuration for `leanprover/comparator` / `lake comparator` (`enable_nanoda: true`). |
| `scripts/verify_challenge.lean` | Checks exact `Expr` equality between `Challenge` and `Solution` plus axiom allowlist. |
| `MaynardDock/BombieriVinogradovAdapter.lean` | Bridges `RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov` ($\psi$-form) to `BombieriVinogradov` ($\pi$-form) for all $\theta < 1/2, A \ge 1$. |
| `MaynardDock/Capstone246.lean` | Zero-parameter unconditional Polymath8b ($H = 246$) theorems. |
| `MaynardDock/Capstone.lean` | Zero-parameter unconditional Maynard ($H = 600$) theorems (faster target). |
| `MaynardDock/Audit.lean` | `#print axioms` census for all top-level `MaynardDock` theorems. |
| `RHDirect/` | Minimal 38-module self-contained Bombieri–Vinogradov / Siegel–Walfisz slice (no unfinished RH drafts). |
| `PrimeGaps/`, `PrimeGapsTheory/`, `PrimeGapsCert/` | Vendored unmodified from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) (Apache-2.0). |

## Hardware Requirements, Build Time & Caches

Measured on an 8-core Intel Core Ultra 7 258V laptop with 32 GB RAM (Lean `v4.33.1`, Mathlib `0df444a3`):

| Step | Wall-clock time | Peak single-process RSS | Notes |
| :--- | :--- | :--- | :--- |
| `lake exe cache get` | ~1–2 min | < 1 GB | Downloads prebuilt **Mathlib** `.olean` cache (strongly recommended!). |
| `lake build` (full from source, with Mathlib cache) | ~18 min (8 cores) | ~6.2 GB | Compiles 38 `RHDirect` + `PrimeGapsTheory` + `PrimeGapsCert` + `MaynardDock` + `Solution`. Total RAM across parallel workers reaches ~16–24 GB on 8 cores. |
| `lake env lean --run scripts/verify_challenge.lean` | ~17 s | ~8.4 GB | Verifies exact `Challenge` ↔ `Solution` type match and axiom allowlist. |
| `lake env leanchecker --fresh Solution` | ~10 min | ~8.4 GB | Replays every transitive declaration into a fresh Lean 4 kernel. |
| `lean4export` + `nanoda` (Rust kernel) | ~4.3 min export + ~1.1 min check | ~5.3 GB | Independent Rust kernel (`nanoda_lib`), checks all 89,600 declarations with `{propext, Classical.choice, Quot.sound}` only. |

**RAM guidance:**
- **Recommended:** **32 GB RAM** (runs smoothly at full parallelism).
- **16 GB RAM:** Set `export LEAN_NUM_THREADS=2` before `lake build` (and make sure swap is enabled) to avoid OOM when heavy modules compile concurrently.
- **Prebuilt caches:** Upstream Mathlib `.olean`s are fetched automatically by `lake exe cache get`. Project-level `.olean`s (`RHDirect`, `PrimeGaps*`, `MaynardDock`) are built from source (and cached across runs in GitHub Actions via `lean-action`).

## Reproduce & Verify Locally

```sh
git clone https://github.com/nil-commits/maynardlean4.git
cd maynardlean4

# 1. Fetch prebuilt Mathlib .olean cache (do NOT skip unless you want to compile Mathlib!)
lake exe cache get

# 2. Build the full unconditional H = 246 proof (use LEAN_NUM_THREADS=2 on 16 GB machines)
lake build

# 3. Verify Challenge.lean ↔ Solution.lean exact type match and axioms
lake build Challenge MaynardDock.Audit
lake env lean --run scripts/verify_challenge.lean

# 4. Full fresh Lean 4 kernel replay
lake env leanchecker --fresh Solution
```

For independent Rust-kernel verification (`lean4export` + `nanoda`), see `.github/workflows/ci.yml` or run [`Comparator/comparator.json`](Comparator/comparator.json) with `leanprover/comparator` / `lake comparator`.

## Third-Party Attribution & License

- Repository license: **Apache-2.0** (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
- `PrimeGaps/`, `PrimeGapsTheory/`, and `PrimeGapsCert/` are vendored unmodified from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) (Copyright 2026 Axiom Math, Apache-2.0).
- `RHDirect/` is a minimal 38-module analytic number theory slice extracted from [`nil-commits/alpoge-rh-golf`](https://github.com/nil-commits/alpoge-rh-golf) (`rh-direct-v1.2.0`).
- `PrimeNumberTheoremAnd` uses [`nil-commits/PrimeNumberTheoremAnd`](https://github.com/nil-commits/PrimeNumberTheoremAnd) (`6c89d569`), a public fork of `AxiomMath/PrimeNumberTheoremAnd` applying a 1-line `MediumPNT.lean` compatibility fix for Mathlib `v4.33.1`.
