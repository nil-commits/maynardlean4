# maynardlean4: Unconditional Bounded Prime Gaps ($H = 246$) in Lean 4

[![Trustless Verification CI](https://github.com/nil-commits/maynardlean4/actions/workflows/ci.yml/badge.svg)](https://github.com/nil-commits/maynardlean4/actions/workflows/ci.yml)

A **zero-parameter, unconditional** Lean 4 proof of Polymath8b / Maynard–Tao's Bounded Prime Gaps theorem ($H = 246$), verified by **two independent type checkers**: the official Lean 4 kernel (`leanchecker --fresh`) and the independent Rust kernel [`nanoda`](https://github.com/ammkrn/nanoda_lib) (89,600 transitive declarations checked, 0 errors).

> **Status: independent formalization, not a first.** The theorem is Polymath8b (2014), not new mathematics, and an unconditional $H = 246$ proof in Lean 4 with the standard axioms already existed before this repository. See [Status & prior work](#status--prior-work). What this repository contributes is a self-contained *build* on a **different Bombieri–Vinogradov lineage** (`RHDirect`) plus the adapter that discharges the B–V hypothesis, together with the verification harness.

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

## What this repository adds

The Maynard–Tao sieve, the $M_{50,\,1/25} > 4$ certificate, and the $H = 246$ endgame are **vendored unmodified** from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib). That library is **Bombieri–Vinogradov-conditional**: `BombieriVinogradov` is a named hypothesis in its `Challenge.lean`. This repository supplies the missing half along an independent path:

1. **`RHDirect/`** — a 38-module analytic number theory slice (extracted from the Alpöge–Claude archive, `rh-direct-v1.2.0`) proving an unconditional $\psi$-form Bombieri–Vinogradov theorem.
2. **`MaynardDock/BombieriVinogradovAdapter.lean`** — an exact Abel-summation and level-geometry bridge from the $\psi$-form estimate to the $\pi$-form `BombieriVinogradov` proposition for all $\theta < 1/2$, $A \ge 1$.
3. **`MaynardDock/Capstone246.lean`**, **`Solution.lean`** — zero-parameter capstones and the discharge of `Challenge.lean`.
4. **The verification harness** — `leanchecker --fresh`, `nanoda`, the axiom allowlist, and `scripts/verify_challenge.lean`.

It does **not** add new mathematics, a new sieve, or a new numerical certificate.

## Status & prior work

| Date | Artifact | What it establishes | Axioms |
| :--- | :--- | :--- | :--- |
| 2026-07 | [`jyh/salt`](https://github.com/jyh/salt) (`Salt.SW.bounded_gaps_unconditional`) | Unconditional bounded gaps, closed (`0` binders) — but `∃ C`, **no explicit 246**; public since 2026-08-16, described in [arXiv:2608.21356](https://arxiv.org/abs/2608.21356) | `{propext, Classical.choice, Quot.sound}` |
| 2026-08-08 | [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) | $H \le 246$ **conditional** on `BombieriVinogradov` (a named hypothesis) | `{propext, Classical.choice, Quot.sound}` |
| 2026-08-31 | [`kimihiro64/bombieri-vinogradov`](https://github.com/kimihiro64/bombieri-vinogradov) (commit `7a174830`, 2026-09-05) | Unconditional Bombieri–Vinogradov for every $\theta < 1/2$ | `{propext, Classical.choice, Quot.sound}` |
| **2026-10-05** | [lean-eval submission #1971](https://github.com/leanprover/lean-eval-submissions/issues/1971) (`zhang_bounded_prime_gaps`) | **Unconditional $H = 246$**, combining `PrimeGapsLib` + `kimihiro64/bombieri-vinogradov`; accepted by the official comparator (`pass`) | `{propext, Classical.choice, Quot.sound}` |
| 2026-11-05 | [`BigO-Hunter/prime-gaps-246-lean`](https://github.com/BigO-Hunter/prime-gaps-246-lean) | Same combination, submission layout | — |
| 2026-11-23 | this repository | Unconditional $H = 246$ via `PrimeGapsLib` + `RHDirect` (different B–V formalization) | `{propext, Classical.choice, Quot.sound}` |

In particular: **AxiomMath's library alone is indeed conditional, but it was made unconditional with `kimihiro64/bombieri-vinogradov` and accepted by the official lean-eval comparator on 2026-10-05**, seven weeks before this repository. `jyh/salt` had an unconditional bounded-gaps theorem (without an explicit value of $C$) earlier still. This repository should be read as an **independent derivation through a different B–V formalization**, not as a first.

## Architecture

This repository builds as a single unit: apart from Mathlib and a pinned fork of `PrimeNumberTheoremAnd`, every Lean source it needs is vendored. That is a statement about the **build**, not about authorship — the sieve, the certificate, and the endgame are AxiomMath's, and `RHDirect` is extracted from the Alpöge archive.

```text
RHDirect/ (38-module analytic NT slice: unconditional Bombieri–Vinogradov, ψ-form)
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
| `RHDirect/` | Minimal 38-module Bombieri–Vinogradov / Siegel–Walfisz slice (no unfinished RH drafts). |
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
- Prior work referenced above is not vendored here; `kimihiro64/bombieri-vinogradov`, `jyh/salt`, and the lean-eval submission are independent artifacts and are linked for provenance only.
