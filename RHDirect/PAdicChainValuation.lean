import RHDirect.Interfaces
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# RHDirect.PAdicChainValuation

Direct, compact, 0-`sorry`, 0-`axiom` rebuild of the **$p$-adic Valuation & Divisibility
Accumulation Engine Along the Iterated Theta-Lift Chain** against `RHDirect.Interfaces`
and Mathlib `v4.33.1`.

## Contents

1. **Iterated Column-Chain & Sharp Valuation Accumulation (`chain_into`)**:
   - Clean abstract discrete-valuation (`AddValuation LL (WithTop ℤ)`) and integral-lattice
     chain system `ChainValuationSystem`, tracking `m` iterated lift steps `colUp i` and
     Hecke/U-operator products `Uprod i A`.
   - Exact commutation induction (`Uprod_comm`, `Uprod_colUp`), sharp `m`-step lattice
     preservation (`chain_into`), triangular-number exponent formula (`chain_loss_formula`),
     valuation-ring division (`quot_mem_valRing`), and the sharp column-valuation theorem
     (`levelChainSharpColumnValuation_of_stability`) showing how division in a single common
     integral lattice avoids paying `m` separate integrality penalties (breaking the `2/3` barrier,
     proved quantitatively in `separate_vs_common_lattice_saving`).

2. **Exact Legendre, `padicValNat`, Ultrametric Norm & Dwork Power-Series Valuation Bounds**:
   - Ultrametric prime-power norm identity `norm_natCast_eq_pow_padicValNat`.
   - Sharp two-sided Legendre factorial valuation bounds:
     `padicValNat_factorial_upper` (`v_l(k!) ≤ (k - 1) / (l - 1)`) and
     `padicValNat_factorial_lower` (`k / (l - 1) - (log_l k + 1) ≤ v_l(k!)`),
     plus multi-index factorial norm bound `multifactorial_norm_bound`.
   - Dwork multivariate power-series weight calculus (`MonoWtGe`, `WtGeLe`, `WtGe`):
     Cauchy-product additivity (`multiplicative_weight_le`), power scaling (`wtGeLe_pow`),
     Dwork exponential integrality (`dwork_exp_weight_le`), and Dwork logarithm reverse
     induction (`dwork_log_weight_induction`).
   - Young diagram jet-column identities (`young_second_row_length_count`, `young_size_eq_sum_colLen`).

3. **Selmer/Vandiver Divisibility Budget (`vvRecord` & `divinN_of_hypV`)**:
   - Direct deduction of summability and total prime-weighted Sha bound (`vvRecord_of_VVle`)
     from `RHDirect.VVle`.
   - Asymptotic `log x ^ 2 ≤ x ^ ε` (`log_sq_le_rpow`) and exact divisibility-budget transfer
     (`divinN_at_of_linkN`, `divinN_of_vAt`) from `RHDirect.VAt` into the `DIVinN` envelope.

4. **Common-Slope Cancellation Arithmetic (`Ga_bound5` & `key_identity5`)**:
   - Clean, direct formalization of `LevelOfCongruence.lean` (`Lam5`, `K5v5`, `K0v5`, `K7v5`,
     `s_lower5`, `Vvar_bound5`, `u_function_le_mean`, `key_identity5`, `Ga_bound5`,
     `weighted_mean_lower_bound_le`) against `RHDirect.BostSlopeFiber`, isolating the exact
     cancellation of the common dual-lattice slope `muCC u0` and the `m * sumA * lg` term.
-/

open Real Finset
open scoped BigOperators

namespace RHDirect.PAdicChainValuation

noncomputable section

/-! ## Section 1: Iterated Column-Chain & Sharp Valuation Accumulation (`chain_into`) -/

/-- Valuation subring `{x : LL | 0 ≤ v x}` attached to an additive valuation `v : AddValuation LL (WithTop ℤ)`. -/
def valSubring {LL : Type*} [Field LL] (v : AddValuation LL (WithTop ℤ)) : Subring LL where
  carrier := {x : LL | (0 : WithTop ℤ) ≤ v x}
  mul_mem' {a b} ha hb := by
    show (0 : WithTop ℤ) ≤ v (a * b)
    rw [AddValuation.map_mul]
    exact add_nonneg ha hb
  one_mem' := by
    show (0 : WithTop ℤ) ≤ v 1
    rw [AddValuation.map_one]
  add_mem' {a b} ha hb := by
    show (0 : WithTop ℤ) ≤ v (a + b)
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by
    show (0 : WithTop ℤ) ≤ v 0
    rw [AddValuation.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    show (0 : WithTop ℤ) ≤ v (-a)
    rwa [AddValuation.map_neg]

/-- Abstract algebraic data for an `m`-step iterated theta-lift column chain over a field `K`
with an embedded valuation field `LL →+* K`, prime `T` of ramification index `ramIdx`,
rank-stepped spaces `Fn i`, transition maps `KT i`, U-operators `Uop i v`, and integral
lattices `S i` over the valuation ring `valSubring val`. -/
structure ChainValuationSystem (K LL ι : Type*) [Field K] [Field LL] where
  /-- Length of the iterated lift chain. -/
  m : ℕ
  /-- Prime whose powers control the sharp column valuation. -/
  T : ℕ
  T_prime : T.Prime
  /-- Discrete additive valuation on `LL`. -/
  val : AddValuation LL (WithTop ℤ)
  /-- Ramification index `e_w` at the place above `T`, so `val (T : LL) = e_w`. -/
  ramIdx : ℕ
  val_T : val (T : LL) = ((ramIdx : ℤ) : WithTop ℤ)
  /-- Field embedding `LL →+* K` (e.g., `LL ↪ ℂ`). -/
  embK : LL →+* K
  /-- Spaces of forms along the chain `0, 1, ..., m`. -/
  Fn : ℕ → Type
  [addCommGroupFn : ∀ i, AddCommGroup (Fn i)]
  [moduleFn : ∀ i, Module K (Fn i)]
  /-- Rational/automorphic subspaces `Fi i ⊆ Fn i` preserved by `Uop` and `KT`. -/
  Fi : ∀ i, Submodule K (Fn i)
  /-- Lift transition operators `KT i : Fn i →ₗ[K] Fn (i + 1)`. -/
  KT : ∀ i, Fn i →ₗ[K] Fn (i + 1)
  /-- Commuting Hecke/U-operators indexed by `ι` at each level `i`. -/
  Uop : ∀ i, ι → (Fn i →ₗ[K] Fn i)
  /-- Integral lattices `Vl i` with `valSubring val`-linear embeddings into `Fn i`. -/
  Vl : ℕ → Type
  [addCommGroupVl : ∀ i, AddCommGroup (Vl i)]
  [moduleVl : ∀ i, Module (valSubring val) (Vl i)]
  /-- Embedding of integral lattice `Vl i` into `Fn i` (semilinear along `valSubring val →+* K`). -/
  embV : ∀ i, Vl i →ₛₗ[embK.comp (valSubring val).subtype] Fn i
  /-- Integral lattice image lands inside the automorphic subspace `Fi i`. -/
  embV_mem_Fi : ∀ i (x : Vl i), embV i x ∈ Fi i
  /-- Distinguished integral sublattices `S i ⊆ Vl i` tracked along the chain. -/
  S : ∀ i, Submodule (valSubring val) (Vl i)

attribute [instance] ChainValuationSystem.addCommGroupFn ChainValuationSystem.moduleFn
  ChainValuationSystem.addCommGroupVl ChainValuationSystem.moduleVl

namespace ChainValuationSystem

variable {K LL ι : Type*} [Field K] [Field LL] (X : ChainValuationSystem K LL ι)

/-- Iterated column-chain operator `colUp i : Fn 0 →ₗ[K] Fn i`, composing `KT (i-1) ∘ ⋯ ∘ KT 0`. -/
def colUp (i : ℕ) : X.Fn 0 →ₗ[K] X.Fn i :=
  Nat.rec (motive := fun j => X.Fn 0 →ₗ[K] X.Fn j) LinearMap.id (fun j g => X.KT j ∘ₗ g) i

@[simp] theorem colUp_zero (φ : X.Fn 0) : X.colUp 0 φ = φ := rfl

@[simp] theorem colUp_succ (i : ℕ) (φ : X.Fn 0) :
    X.colUp (i + 1) φ = X.KT i (X.colUp i φ) := rfl

/-- Ordered composition of U-operators along a list `A : List ι` at level `i`. -/
def Uprod (i : ℕ) (A : List ι) : X.Fn i →ₗ[K] X.Fn i :=
  A.foldr (fun v g => (X.Uop i v).comp g) LinearMap.id

/-- Stability of the automorphic subspaces `Fi i` under `Uop` and `KT` for `i ≤ m`. -/
def FormsStable : Prop :=
  (∀ i, i ≤ X.m → ∀ v φ, φ ∈ X.Fi i → X.Uop i v φ ∈ X.Fi i) ∧
  (∀ i, i < X.m → ∀ φ, φ ∈ X.Fi i → X.KT i φ ∈ X.Fi (i + 1))

/-- Single-step commutation between `Uop` and `KT` with prime power factor `(T : K) ^ s`
(where `t + 1 = 2 * s` in the unitary theta-lift chain). -/
def UOpCommutes (s : ℕ) : Prop :=
  ∀ i, i < X.m → ∀ v φ, φ ∈ X.Fi i →
    X.Uop (i + 1) v (X.KT i φ) = (X.T : K) ^ s • X.KT i (X.Uop i v φ)

/-- A map `f : Fn i → Fn j` sends integral lattice `S i` into `S j` modulo `embV`. -/
def Into (i j : ℕ) (f : X.Fn i → X.Fn j) : Prop :=
  ∀ x ∈ X.S i, ∃ y ∈ X.S j, X.embV j y = f (X.embV i x)

theorem Uprod_mem (hF : X.FormsStable) {i : ℕ} (hi : i ≤ X.m) (A : List ι) {φ : X.Fn i}
    (hφ : φ ∈ X.Fi i) : X.Uprod i A φ ∈ X.Fi i := by
  induction A with
  | nil => exact hφ
  | cons v l ih =>
    simpa [Uprod] using hF.1 i hi v _ ih

theorem Upow_mem (hF : X.FormsStable) (A : List ι) (n : ℕ) {φ : X.Fn 0}
    (hφ : φ ∈ X.Fi 0) : ((X.Uprod 0 A) ^ n) φ ∈ X.Fi 0 := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    rw [pow_succ']
    exact X.Uprod_mem hF (Nat.zero_le _) A ih

theorem colUp_mem (hF : X.FormsStable) {i : ℕ} (hi : i ≤ X.m) {φ : X.Fn 0}
    (hφ : φ ∈ X.Fi 0) : X.colUp i φ ∈ X.Fi i := by
  induction i with
  | zero => exact hφ
  | succ i ih =>
    exact hF.2 i hi _ (ih (Nat.le_of_succ_le hi))

/-- Commuting a list product `Uprod (i + 1) A` past one lift step `KT i` produces
`(T : K) ^ (s * A.length)`. -/
theorem Uprod_comm (hF : X.FormsStable) {s : ℕ} (hComm : X.UOpCommutes s)
    {i : ℕ} (hi : i < X.m) (A : List ι) {φ : X.Fn i} (hφ : φ ∈ X.Fi i) :
    X.Uprod (i + 1) A (X.KT i φ) = (X.T : K) ^ (s * A.length) • X.KT i (X.Uprod i A φ) := by
  induction A with
  | nil => simp [Uprod]
  | cons v l ih =>
    change X.Uop (i + 1) v (X.Uprod (i + 1) l (X.KT i φ)) =
      (X.T : K) ^ (s * (v :: l).length) • X.KT i (X.Uop i v (X.Uprod i l φ))
    rw [ih, map_smul, hComm i hi v _ (X.Uprod_mem hF hi.le l hφ), smul_smul, ← pow_add,
      List.length_cons, Nat.mul_succ]

/-- Commuting `Uprod i A` all the way from level `i` back to level `0` along `colUp i`
accumulates the exact prime power `(T : K) ^ (s * A.length * i)`. -/
theorem Uprod_colUp (hF : X.FormsStable) {s : ℕ} (hComm : X.UOpCommutes s)
    {i : ℕ} (hi : i ≤ X.m) (A : List ι) {φ : X.Fn 0} (hφ : φ ∈ X.Fi 0) :
    X.Uprod i A (X.colUp i φ) = (X.T : K) ^ (s * A.length * i) • X.colUp i (X.Uprod 0 A φ) := by
  induction i with
  | zero => simp [colUp]
  | succ i ih =>
    have hi' : i < X.m := hi
    rw [colUp_succ, X.Uprod_comm hF hComm hi' A (X.colUp_mem hF hi'.le hφ), ih hi'.le,
      map_smul, smul_smul, ← pow_add, Nat.mul_succ, Nat.add_comm (s * A.length)]
    rfl

/-- **Core `m`-Step Sharp Column-Valuation Induction (`chain_into`)**:
If at every step `i < m` the operator `(T : K) ^ e • Uprod (i + 1) A (KT i ·)` preserves the
integral lattices `S i → S (i + 1)`, then after `i` steps
`(T : K) ^ (i * e + s * A.length * ∑ j ∈ range (i + 1), j) • colUp i ((Uprod 0 A ^ i) ·)`
maps `S 0` directly into `S i`. -/
theorem chain_into (hF : X.FormsStable) {s : ℕ} (hComm : X.UOpCommutes s)
    (A : List ι) (e : ℕ)
    (hU : ∀ i, i < X.m → X.Into i (i + 1) (fun φ => (X.T : K) ^ e • X.Uprod (i + 1) A (X.KT i φ)))
    {i : ℕ} (hi : i ≤ X.m) :
    X.Into 0 i (fun φ =>
      (X.T : K) ^ (i * e + s * A.length * ∑ j ∈ Finset.range (i + 1), j) •
        X.colUp i (((X.Uprod 0 A) ^ i) φ)) := by
  induction i with
  | zero =>
    intro x hx
    exact ⟨x, hx, by simp [colUp]⟩
  | succ i ih =>
    have hi' : i < X.m := hi
    intro x hx
    obtain ⟨y, hy, hy'⟩ := ih hi'.le x hx
    obtain ⟨z, hz, hz'⟩ := hU i hi' y hy
    refine ⟨z, hz, ?_⟩
    have hm := X.Upow_mem hF A i (X.embV_mem_Fi 0 x)
    have key := X.Uprod_colUp hF hComm hi A hm
    rw [hz']
    beta_reduce at hy' ⊢
    rw [hy', map_smul, map_smul, ← colUp_succ, key, pow_succ' (X.Uprod 0 A) i,
      Module.End.mul_apply, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Finset.sum_range_succ _ (i + 1)]
    congr 2
    ring

/-- Closed-form triangular-number identity for the accumulated valuation loss along `m` steps:
`m * e + s * d * ∑_{j=0}^m j = m * (e + s * d * (m + 1) / 2)`. -/
theorem chain_loss_formula (m e s d : ℕ) :
    ((m * e + s * d * ∑ j ∈ Finset.range (m + 1), j : ℕ) : ℝ) =
      (m : ℝ) * ((e : ℝ) + (s : ℝ) * (d : ℝ) * ((m : ℝ) + 1) / 2) := by
  have htri : ((∑ j ∈ Finset.range (m + 1), j : ℕ) : ℝ) * 2 = ((m : ℝ) + 1) * (m : ℝ) := by
    have h := Finset.sum_range_id_mul_two (m + 1)
    rw [Nat.add_sub_cancel] at h
    exact_mod_cast h
  generalize (∑ j ∈ Finset.range (m + 1), j : ℕ) = S at htri ⊢
  push_cast
  linear_combination ((s : ℝ) * (d : ℝ) / 2) * htri

/-- Exact valuation of a prime power `(T : LL) ^ k` in `AddValuation`: `val (T^k) = ramIdx * k`. -/
theorem val_pow_T (k : ℕ) :
    X.val ((X.T : LL) ^ k) = (((X.ramIdx * k : ℕ) : ℤ) : WithTop ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, X.val_T, ← WithTop.coe_add]
    congr 1

/-- **Compatible Common-Lattice Division**: If `c ∈ LL` has discrete valuation `val c = n` with
`ramIdx * b ≤ n`, then `c * T ^ a * (T ^ b)⁻¹` lies in the valuation subring `valSubring val`. -/
theorem quot_mem_valRing {c : LL} {n : ℤ} (hc : X.val c = (n : WithTop ℤ)) (a b : ℕ)
    (h : ((X.ramIdx * b : ℕ) : ℤ) ≤ n) :
    c * (X.T : LL) ^ a * ((X.T : LL) ^ b)⁻¹ ∈ valSubring X.val := by
  show (0 : WithTop ℤ) ≤ X.val _
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hc, X.val_pow_T a,
    X.val_pow_T b]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  have ha : (0 : ℤ) ≤ ((X.ramIdx * a : ℕ) : ℤ) := Int.natCast_nonneg _
  exact_mod_cast (by omega :
    (0 : ℤ) ≤ n + ((X.ramIdx * a : ℕ) : ℤ) + -((X.ramIdx * b : ℕ) : ℤ))

/-- **Full Sharp Column-Valuation Theorem (`levelChainSharpColumnValuation_of_stability`)**:
Under `FormsStable`, `UOpCommutes s`, and one-step lattice preservation `hU`, if `c ∈ LL` has
valuation `n ≥ ramIdx * (m * e + s * A.length * ∑_{j=0}^m j)`, then for every `x ∈ S 0` and
every `a : ℕ`, the lifted & divided form
`embK c * T ^ a • colUp m ((Uprod 0 A ^ m) (embV 0 x))` lies directly inside the single
common integral lattice `embV m (S m)`. -/
theorem levelChainSharpColumnValuation_of_stability [CharZero K]
    (hF : X.FormsStable) {s : ℕ} (hComm : X.UOpCommutes s)
    (A : List ι) (e a : ℕ)
    (hU : ∀ i, i < X.m → X.Into i (i + 1) (fun φ => (X.T : K) ^ e • X.Uprod (i + 1) A (X.KT i φ)))
    {c : LL} {n : ℤ} (hc : X.val c = (n : WithTop ℤ))
    (hn : ((X.ramIdx * (X.m * e + s * A.length * ∑ j ∈ Finset.range (X.m + 1), j) : ℕ) : ℤ) ≤ n)
    {x : X.Vl 0} (hx : x ∈ X.S 0) :
    ∃ z ∈ X.S X.m,
      X.embV X.m z =
        (X.embK c * (X.T : K) ^ a) • X.colUp X.m (((X.Uprod 0 A) ^ X.m) (X.embV 0 x)) := by
  set b := X.m * e + s * A.length * ∑ j ∈ Finset.range (X.m + 1), j with hb
  obtain ⟨y, hy, hy'⟩ := X.chain_into hF hComm A e hU (le_refl X.m) x hx
  have hmem : c * (X.T : LL) ^ a * ((X.T : LL) ^ b)⁻¹ ∈ valSubring X.val :=
    X.quot_mem_valRing hc a b hn
  refine ⟨(⟨_, hmem⟩ : valSubring X.val) • y, (X.S X.m).smul_mem _ hy, ?_⟩
  have hT : (X.T : K) ^ b ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr X.T_prime.ne_zero)
  rw [LinearMap.map_smulₛₗ]
  change X.embK (c * (X.T : LL) ^ a * ((X.T : LL) ^ b)⁻¹) • X.embV X.m y = _
  rw [hy', smul_smul]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  field_simp
  rw [hb]

end ChainValuationSystem

/-- **Why Common-Lattice Division Breaks the `2/3` Barrier**:
If a fixed integrality penalty `P > 0` were paid separately at each of `m` steps (`m * P` total),
balancing against `x / m` forces `max (x / m) (m * P) ≥ √(P * x)` (and for `P = m`, forces
`x ^ (2/3)`). By contrast, compatible division in ONE common integral lattice pays `P` once,
yielding amortized per-step cost `(x + P) / m` — which at `m = √x` beats `x ^ (2/3)` whenever
`P ≤ x` and `x > 8`. -/
theorem separate_vs_common_lattice_saving {x m P : ℝ} (hx : 0 < x) (hm : 0 < m) (hP : 0 < P) :
    Real.sqrt (P * x) ≤ max (x / m) (m * P) ∧
      (m = Real.sqrt x → P ≤ x → (x + P) / m ≤ 2 * Real.sqrt x) := by
  constructor
  · by_cases h : m ≤ Real.sqrt (x / P)
    · refine le_trans ?_ (le_max_left _ _)
      rw [le_div_iff₀ hm]
      have hsq : Real.sqrt (P * x) * Real.sqrt (x / P) = x := by
        rw [← Real.sqrt_mul (mul_nonneg hP.le hx.le)]
        have : P * x * (x / P) = x ^ 2 := by field_simp
        rw [this, Real.sqrt_sq hx.le]
      calc Real.sqrt (P * x) * m
          ≤ Real.sqrt (P * x) * Real.sqrt (x / P) :=
            mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
        _ = x := hsq
    · push Not at h
      refine le_trans ?_ (le_max_right _ _)
      have hsq : Real.sqrt (x / P) * P = Real.sqrt (P * x) := by
        have h1 : Real.sqrt (x / P) * Real.sqrt (P ^ 2) = Real.sqrt (P * x) := by
          rw [← Real.sqrt_mul (div_nonneg hx.le hP.le)]
          congr 1
          field_simp
        rwa [Real.sqrt_sq hP.le] at h1
      calc Real.sqrt (P * x) = Real.sqrt (x / P) * P := hsq.symm
        _ ≤ m * P := mul_le_mul_of_nonneg_right h.le hP.le
  · rintro rfl hPx
    have hsqpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    rw [div_le_iff₀ hsqpos]
    have hmul : 2 * Real.sqrt x * Real.sqrt x = 2 * x := by
      rw [mul_assoc, Real.mul_self_sqrt hx.le]
    linarith

/-! ## Section 2: Exact Legendre, `padicValNat`, Ultrametric Norm & Dwork Power-Series Bounds -/

section UltrametricAndLegendre

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- In any ultrametric normed field, every natural number has norm at most `1`. -/
theorem norm_natCast_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

/-- In any ultrametric normed field, every integer has norm at most `1`. -/
theorem norm_intCast_le_one (z : ℤ) : ‖(z : K)‖ ≤ 1 := by
  cases z with
  | ofNat n => simpa using norm_natCast_le_one (K := K) n
  | negSucc n =>
    rw [Int.cast_negSucc, norm_neg]
    exact norm_natCast_le_one (K := K) (n + 1)

/-- If `l` is prime with `‖(l : K)‖ < 1` and `¬ l ∣ m`, then `‖(m : K)‖ = 1` (via Bézout). -/
theorem norm_natCast_eq_one_of_not_dvd {l m : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  apply le_antisymm (norm_natCast_le_one m)
  by_contra hltm
  push Not at hltm
  have hcop : Nat.Coprime l m := hl.coprime_iff_not_dvd.mpr hm
  have hbez : (1 : ℤ) = (l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m := by
    have h := Nat.gcd_eq_gcd_ab l m
    rw [hcop.gcd_eq_one] at h
    exact_mod_cast h
  have hK : (1 : K) = (l : K) * (Nat.gcdA l m : K) + (m : K) * (Nat.gcdB l m : K) := by
    have := congrArg (Int.cast (R := K)) hbez
    simpa using this
  have h1 : ‖(l : K) * (Nat.gcdA l m : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖(Nat.gcdA l m : K)‖
        ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left (norm_intCast_le_one _) (norm_nonneg _)
      _ < 1 := by linarith
  have h2 : ‖(m : K) * (Nat.gcdB l m : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(m : K)‖ * ‖(Nat.gcdB l m : K)‖
        ≤ ‖(m : K)‖ * 1 := mul_le_mul_of_nonneg_left (norm_intCast_le_one _) (norm_nonneg _)
      _ < 1 := by linarith
  have h3 : ‖(1 : K)‖ < 1 := by
    rw [hK]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  rw [norm_one] at h3
  exact lt_irrefl 1 h3

/-- **Exact Ultrametric Prime-Power Norm Formula**:
For any prime `l` with `‖(l : K)‖ < 1` and any `n ≠ 0`, `‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n`. -/
theorem norm_natCast_eq_pow_padicValNat {l n : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hn : n ≠ 0) : ‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n := by
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n l
  have hnd := Nat.not_dvd_ordCompl hl hn
  rw [Nat.factorization_def n hl] at hfac hnd
  conv_lhs => rw [← hfac]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow,
    norm_natCast_eq_one_of_not_dvd hl hlt hnd, mul_one]

end UltrametricAndLegendre

/-- **Legendre Upper Bound**: For prime `l` and `k ≠ 0`,
`v_l(k!) ≤ (k - 1) / (l - 1)`. -/
theorem padicValNat_factorial_upper {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : k ≠ 0) :
    (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) / ((l : ℝ) - 1) := by
  have : Fact l.Prime := ⟨hl⟩
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk
  have hl2 : 2 ≤ l := hl.two_le
  have h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1 := by omega
  have h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l),
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk), Nat.cast_one] at h2
  have hpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
    linarith
  rw [le_div_iff₀ hpos, mul_comm]
  exact h2

/-- Weak Legendre upper bound `v_l(k!) ≤ k / (l - 1)` valid for all `k : ℕ` (including `k = 0`). -/
theorem padicValNat_factorial_le_div {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) / ((l : ℝ) - 1) := by
  have hlpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · calc (padicValNat l k.factorial : ℝ)
        ≤ ((k : ℝ) - 1) / ((l : ℝ) - 1) := padicValNat_factorial_upper hl hk.ne'
      _ ≤ (k : ℝ) / ((l : ℝ) - 1) := by
        apply div_le_div_of_nonneg_right _ hlpos.le
        linarith

/-- **Legendre Lower Bound (via Base-`l` Digit Sum)**:
For prime `l` and `1 ≤ k`,
`k / (l - 1) - (log_l k + 1) ≤ v_l(k!)`. -/
theorem padicValNat_factorial_lower {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) / ((l : ℝ) - 1) - (Real.logb l (k : ℝ) + 1) ≤ (padicValNat l k.factorial : ℝ) := by
  have : Fact l.Prime := ⟨hl⟩
  have hl1 : 1 < l := hl.one_lt
  have hl1R : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
  have hlpos : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hleg := sub_one_mul_padicValNat_factorial (p := l) k
  have hdigits_le : (l.digits k).sum ≤ (l - 1) * (l.digits k).length := by
    have hmem : ∀ d ∈ l.digits k, d ≤ l - 1 := fun d hd => by
      have := Nat.digits_lt_base hl1 hd
      omega
    calc (l.digits k).sum
        ≤ (l.digits k).length * (l - 1) := by
          simpa using List.sum_le_card_nsmul (l.digits k) (l - 1) hmem
      _ = (l - 1) * (l.digits k).length := mul_comm _ _
  have hlen_le : ((l.digits k).length : ℝ) ≤ Real.logb l (k : ℝ) + 1 := by
    have hpos : 0 < (l.digits k).length := by
      rw [List.length_pos_iff_ne_nil]
      exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    set L := (l.digits k).length - 1 with hLdef
    have hL : l ^ L ≤ k := by
      by_contra hlt
      push Not at hlt
      have hle : (l.digits k).length ≤ L := (Nat.digits_length_le_iff hl1 k).mpr hlt
      omega
    have hLR : ((l : ℝ) ^ L) ≤ (k : ℝ) := by exact_mod_cast hL
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hpowpos : (0 : ℝ) < (l : ℝ) ^ L := pow_pos (by linarith) L
    have hlog : (L : ℝ) ≤ Real.logb l (k : ℝ) := by
      have := Real.logb_le_logb_of_le hl1R hpowpos hLR
      rwa [Real.logb_pow, Real.logb_self_eq_one hl1R, mul_one] at this
    have hcast : ((l.digits k).length : ℝ) = (L : ℝ) + 1 := by
      have : (l.digits k).length = L + 1 := by omega
      exact_mod_cast this
    linarith
  have hlegR : ((l : ℝ) - 1) * (padicValNat l k.factorial : ℝ) + ((l.digits k).sum : ℝ) = (k : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hleg
    have hsub : (l.digits k).sum ≤ k := Nat.digit_sum_le l k
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one, Nat.cast_sub hsub] at h
    linarith
  have hsumR : ((l.digits k).sum : ℝ) ≤ ((l : ℝ) - 1) * (Real.logb l (k : ℝ) + 1) := by
    have h1 : ((l.digits k).sum : ℝ) ≤ ((l : ℝ) - 1) * ((l.digits k).length : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hdigits_le
      rwa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one] at h
    exact h1.trans (mul_le_mul_of_nonneg_left hlen_le hlpos.le)
  have hmul : ((l : ℝ) - 1) * ((k : ℝ) / ((l : ℝ) - 1) - (Real.logb l (k : ℝ) + 1)) ≤
      ((l : ℝ) - 1) * (padicValNat l k.factorial : ℝ) := by
    have hcancel : ((l : ℝ) - 1) * ((k : ℝ) / ((l : ℝ) - 1)) = (k : ℝ) :=
      mul_div_cancel₀ _ hlpos.ne'
    nlinarith
  exact le_of_mul_le_mul_left hmul hlpos

/-- Multi-index factorial `κ! = ∏_i (κ i)!`. -/
def mfact {ι : Type*} (κ : ι →₀ ℕ) : ℕ := κ.prod fun _ k => k.factorial

/-- **Multivariate Factorial Valuation Norm Bound** (matching `factorial_valuation_bound`):
For any multi-index `κ : ι →₀ ℕ` over a finite type `ι` and prime `l` with `‖(l : K)‖ < 1`,
`‖(mfact κ : K)‖ ≤ ‖(l : K)‖ ^ (∑ i, κ i / (l - 1) - |ι| * (log_l (deg κ) + 1))`. -/
theorem multifactorial_norm_bound {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CharZero K] {ι : Type*} [Fintype ι] {l : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (κ : ι →₀ ℕ) :
    ‖((mfact κ : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((∑ i : ι, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1)) := by
  classical
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (κ.degree : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos κ.degree with h | h
    · rw [hL, h]; simp
    · have : 0 ≤ Real.logb l (κ.degree : ℝ) := Real.logb_nonneg hl1 (by exact_mod_cast h)
      linarith
  have hcoord : ∀ i ∈ κ.support,
      ‖(((κ i).factorial : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := padicValNat_factorial_lower hl hki
    have hdeg : (κ i : ℝ) ≤ (κ.degree : ℝ) := by
      have : κ i ≤ κ.degree := by
        rw [Finsupp.degree_apply]
        exact Finset.single_le_sum (f := fun j => κ j) (fun j _ => Nat.zero_le _) hi
      exact_mod_cast this
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (κ.degree : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) hdeg
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i : ι, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i : ι, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

/-! ### Dwork Power-Series Weight Calculus -/

section DworkWeights

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

/-- Linear radius pairing `⟨n, r⟩ = ∑_{i ∈ supp(n)} n(i) * r(i)`. -/
def wtDot (n : ι →₀ ℕ) (r : ι → ℝ) : ℝ := n.sum fun i k => (k : ℝ) * r i

@[simp] theorem wtDot_zero (r : ι → ℝ) : wtDot (0 : ι →₀ ℕ) r = 0 := by
  simp [wtDot]

theorem wtDot_add (n₁ n₂ : ι →₀ ℕ) (r : ι → ℝ) :
    wtDot (n₁ + n₂) r = wtDot n₁ r + wtDot n₂ r := by
  classical
  unfold wtDot
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i a b; push_cast; ring

/-- Coefficient-level Dwork weight lower bound: `‖c‖ ≤ pi ^ (w - ⟨n, r⟩)`. -/
def MonoWtGe (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) : Prop :=
  ‖c‖ ≤ pi ^ (w - wtDot n r)

/-- Truncated power-series weight lower bound for all `n ≤ κ`. -/
def WtGeLe (pi : ℝ) (r : ι → ℝ) (w : ℝ) (κ : ι →₀ ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, n ≤ κ → MonoWtGe pi r w n (MvPowerSeries.coeff n f)

/-- Global power-series weight lower bound for all multi-indices `n`. -/
def WtGe (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, MonoWtGe pi r w n (MvPowerSeries.coeff n f)

/-- Ultrametric finite-sum bound for any `Finset`. -/
lemma ultrametric_norm_sum_le {α : Type*} (s : Finset α) (f : α → K) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ a ∈ s, ‖f a‖ ≤ B) : ‖∑ a ∈ s, f a‖ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Ultrametric `finsum` bound. -/
lemma ultrametric_norm_finsum_le {α : Type*} (f : α → K) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ a, ‖f a‖ ≤ B) : ‖∑ᶠ a, f a‖ ≤ B := by
  by_cases hfin : (Function.support f).Finite
  · rw [finsum_eq_sum _ hfin]
    exact ultrametric_norm_sum_le _ _ hB fun a _ => hf a
  · rw [finsum_of_infinite_support hfin, norm_zero]
    exact hB

omit [IsUltrametricDist K] in
theorem wtGe_one {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) :
    WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  intro n
  unfold MonoWtGe
  classical
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp
  · rw [norm_zero]
    exact Real.rpow_nonneg h0.le _

/-- **Multiplicative Dwork Weight Additivity**:
If `f` has weight `≥ w₁` and `g` has weight `≥ w₂` (up to `κ`), then `f * g` has weight `≥ w₁ + w₂`. -/
theorem multiplicative_weight_le {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {w₁ w₂ : ℝ} {κ : ι →₀ ℕ}
    {f g : MvPowerSeries ι K} (hf : WtGeLe pi r w₁ κ f) (hg : WtGeLe pi r w₂ κ g) :
    WtGeLe pi r (w₁ + w₂) κ (f * g) := by
  classical
  intro n hn
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  refine ultrametric_norm_sum_le _ _ (Real.rpow_nonneg h0.le _) fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have h1 : x.1 ≤ κ := le_trans (hx ▸ le_self_add) hn
  have h2 : x.2 ≤ κ := le_trans (hx ▸ le_add_self) hn
  rw [norm_mul, ← hx, wtDot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w₁ - wtDot x.1 r) * pi ^ (w₂ - wtDot x.2 r) :=
        mul_le_mul (hf x.1 h1) (hg x.2 h2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w₁ + w₂ - (wtDot x.1 r + wtDot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring

theorem wtGeLe_pow {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {w : ℝ} {κ : ι →₀ ℕ}
    {f : MvPowerSeries ι K} (hf : WtGeLe pi r w κ f) (k : ℕ) :
    WtGeLe pi r ((k : ℝ) * w) κ (f ^ k) := by
  induction k with
  | zero =>
    intro n _
    simpa using wtGe_one (K := K) h0 r n
  | succ k ih =>
    rw [pow_succ]
    have h := multiplicative_weight_le h0 ih hf
    push_cast
    rwa [add_mul, one_mul]

theorem wtGe_pow {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {w : ℝ}
    {f : MvPowerSeries ι K} (hf : WtGe pi r w f) (k : ℕ) :
    WtGe pi r ((k : ℝ) * w) (f ^ k) :=
  fun n => wtGeLe_pow h0 (fun m _ => hf m) k n le_rfl

/-- Multivariate formal exponential `exp(B) = subst B (PowerSeries.exp K)`. -/
def mvExp [CharZero K] (B : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst B (PowerSeries.exp K)

/-- Exact ultrametric norm of the `k`-th Taylor coefficient `1 / k!` of `exp`. -/
theorem norm_coeff_exp [CharZero K] {l : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div,
    norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero k)]

/-- **Dwork Exponential Weight Integrality (`dwork_exp_weight_le`)**:
If `constantCoeff B = 0` and `B` has Dwork weight `≥ 1 / (l - 1)` up to `κ`, then
`exp(B)` has Dwork weight `≥ 0` up to `κ` — the `k / (l - 1)` weight of `B^k` cancels the
factorial valuation `v_l(k!) ≤ k / (l - 1)` of `1 / k!`! -/
theorem dwork_exp_weight_le [CharZero K] {l : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    {r : ι → ℝ} {κ : ι →₀ ℕ} {B : MvPowerSeries ι K}
    (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hB : WtGeLe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) κ B) :
    WtGeLe ‖(l : K)‖ r 0 κ (mvExp B) := by
  classical
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hs : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  intro n hn
  unfold MonoWtGe mvExp
  rw [PowerSeries.coeff_subst hs]
  refine ultrametric_norm_finsum_le _ (Real.rpow_nonneg hpi0.le _) fun k => ?_
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hlt k]
  have hk := wtGeLe_pow hpi0 hB k n hn
  unfold MonoWtGe at hk
  have hv := padicValNat_factorial_le_div hl k
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖MvPowerSeries.coeff n (B ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - wtDot n r) :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr (pow_nonneg hpi0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - wtDot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hpi0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (0 - wtDot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        have : (k : ℝ) * (1 / ((l : ℝ) - 1)) = (k : ℝ) / ((l : ℝ) - 1) := by ring
        linarith

/-- Truncation of a multivariate power series strictly below total degree `N`. -/
def truncBelow (N : ℕ) (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun n => if n.degree < N then MvPowerSeries.coeff n f else 0

omit [IsUltrametricDist K] in
@[simp] theorem coeff_truncBelow (N : ℕ) (f : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (truncBelow N f) = if n.degree < N then MvPowerSeries.coeff n f else 0 :=
  rfl

/-- `Low N f` means `f` has no nonzero terms of total degree `< N`. -/
def Low (N : ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, n.degree < N → MvPowerSeries.coeff n f = 0

omit [IsUltrametricDist K] in
lemma low_mono {M N : ℕ} {f : MvPowerSeries ι K} (hMN : M ≤ N) (hf : Low N f) : Low M f :=
  fun n hn => hf n (lt_of_lt_of_le hn hMN)

omit [IsUltrametricDist K] in
lemma low_add {N : ℕ} {f g : MvPowerSeries ι K} (hf : Low N f) (hg : Low N g) :
    Low N (f + g) := fun n hn => by rw [map_add, hf n hn, hg n hn, add_zero]

omit [IsUltrametricDist K] in
lemma low_mul {M N : ℕ} {f g : MvPowerSeries ι K} (hf : Low M f) (hg : Low N g) :
    Low (M + N) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = n.degree := by
    rw [← hx, map_add]
  by_cases h1 : x.1.degree < M
  · rw [hf x.1 h1, zero_mul]
  · rw [hg x.2 (by omega), mul_zero]

omit [IsUltrametricDist K] in
lemma low_pow {M : ℕ} {f : MvPowerSeries ι K} (hf : Low M f) (k : ℕ) :
    Low (k * M) (f ^ k) := by
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact low_mul ih hf

/-- **Dwork Logarithm Reverse Induction (`dwork_log_weight_induction`, matching `LogStep.lean`)**:
If `constantCoeff D = 0` and `exp(D) - 1` has Dwork weight `≥ 1 / (l - 1)`, then `D` itself
has Dwork weight `≥ 1 / (l - 1)`. -/
theorem dwork_log_weight_induction [CharZero K] {l : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    {r : ι → ℝ} {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hE : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (mvExp D - 1)) :
    WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) D := by
  classical
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hD1 : Low 1 D := fun n hn => by
    have h0 : n = 0 := by
      ext i
      have hle : n i ≤ n.degree := by
        by_cases hi : i ∈ n.support
        · rw [Finsupp.degree_apply]
          exact Finset.single_le_sum (f := fun j => n j) (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.mp hi]
      have : n i = 0 := by omega
      simpa using this
    subst h0
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    unfold MonoWtGe
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    unfold MonoWtGe
    rw [coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · rw [norm_zero]
      exact Real.rpow_nonneg hpi0.le _
  have hlow : Low N (D - truncBelow N D) := fun m hm => by
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := fun m hm => by
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (by omega) (low_mul ihk hD1))
        (low_mono (by omega) (low_mul (low_pow hT1 (k + 1)) hlow))
  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • MvPowerSeries.coeff n (D ^ k)
    with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h <;> simp [h]
  have ha1 : a 1 = MvPowerSeries.coeff n D := by simp [ha, PowerSeries.coeff_exp]
  have hsum : MvPowerSeries.coeff n (mvExp D) = (∑ᶠ k, b k) + MvPowerSeries.coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]
    simp only [hc, if_pos rfl, ha1]
  have hEq : MvPowerSeries.coeff n D = MvPowerSeries.coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, MvPowerSeries.coeff_one, if_neg hn0, sub_zero, hsum]
    ring
  unfold MonoWtGe
  rw [hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine ultrametric_norm_finsum_le _ (Real.rpow_nonneg hpi0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · rw [norm_zero]
    exact Real.rpow_nonneg hpi0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, MvPowerSeries.coeff_one, if_neg hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
  have hce : MvPowerSeries.coeff n (D ^ k) = MvPowerSeries.coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hpi0 hTw k n
  unfold MonoWtGe at hbd
  have hv := padicValNat_factorial_upper hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hlt k, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖MvPowerSeries.coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - wtDot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr (pow_nonneg hpi0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - wtDot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hpi0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - wtDot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        have h1 : (k : ℝ) * (1 / ((l : ℝ) - 1)) - ((k : ℝ) - 1) / ((l : ℝ) - 1) =
            1 / ((l : ℝ) - 1) := by ring
        linarith

end DworkWeights

/-! ### Young Diagram Jet-Column Combinatorics (`DworkPowerSeriesWeights.lean`) -/

/-- Number of columns of a Young diagram of height `≥ 2` equals the second row length `rowLen 1`. -/
theorem young_second_row_length_count (μ : YoungDiagram) :
    (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => 2 ≤ μ.colLen c)).card = μ.rowLen 1 := by
  rw [← Finset.card_range (μ.rowLen 1)]
  refine Finset.card_bij (fun (c : Fin (μ.rowLen 0)) _ => (c : ℕ)) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    exact hc
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_range] at hb
    refine ⟨⟨b, lt_of_lt_of_le hb (μ.rowLen_anti 0 1 zero_le_one)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (1, b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hb
    exact YoungDiagram.mem_iff_lt_colLen.mp h1

/-- Total cell count of a Young diagram equals the sum of its column lengths. -/
theorem young_size_eq_sum_colLen (μ : YoungDiagram) :
    μ.cells.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have H : ∀ p ∈ μ.cells, p.2 ∈ Finset.range (μ.rowLen 0) := by
    intro p hp
    rw [Finset.mem_range]
    have h0 : (0, p.2) ∈ μ :=
      μ.up_left_mem (Nat.zero_le p.1) le_rfl ((YoungDiagram.mem_cells p).mp hp)
    exact YoungDiagram.mem_iff_lt_rowLen.mp h0
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

/-! ## Section 3: Selmer/Vandiver Divisibility Budget (`vvRecord` & `divinN_of_hypV`) -/

/-- Prime-weighted Selmer/Sha length term `log l * ∑_{1 ≤ e < t} shaLen(E, l, e)` for `l` prime,
and `0` otherwise. -/
def vvTerm (S : SelmerSystem) (E : Type) [Field E] [NumberField E] (t : ℕ) (l : ℕ) : ℝ :=
  if hl : l.Prime then
    Real.log (l : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E ⟨l, hl⟩ e).toNat : ℝ)
  else 0

theorem vvTerm_nonneg (S : SelmerSystem) (E : Type) [Field E] [NumberField E] (t l : ℕ) :
    0 ≤ vvTerm S E t l := by
  unfold vvTerm
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  · exact le_rfl

/-- **`vvRecord` from `RHDirect.VVle`**:
Any `VVle S E t B` bound yields finiteness of all odd/weight-`< t` Sha lengths, summability of
`vvTerm S E t`, and the infinite-series bound `∑' l, vvTerm S E t l ≤ B`. -/
theorem vvRecord_of_VVle {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t : ℕ} {B : ℝ} (h : VVle S E t B) :
    (∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → S.shaLen E l e ≠ ⊤) ∧
      Summable (vvTerm S E t) ∧ ∑' l, vvTerm S E t l ≤ B := by
  obtain ⟨hfin, hsum⟩ := h
  have hpart : ∀ s : Finset ℕ, ∑ l ∈ s, vvTerm S E t l ≤ B := by
    intro s
    classical
    refine le_trans ?_ (hsum (s.subtype Nat.Prime))
    rw [← Finset.sum_filter_of_ne (p := Nat.Prime) (fun l _ hne => by
      by_contra hl
      exact hne (by unfold vvTerm; simp [hl])), ← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_le_sum fun l _ => ?_
    unfold vvTerm
    rw [dif_pos l.2]
  exact ⟨hfin, summable_of_sum_le (vvTerm_nonneg S E t) hpart,
    Real.tsum_le_of_sum_le (vvTerm_nonneg S E t) hpart⟩

/-- Asymptotic dominance `(log x)^2 ≤ x ^ ε` for any `ε > 0` (matching `DivinNOfHypV.lean`). -/
theorem log_sq_le_rpow {eps : ℝ} (h : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Real.log x ^ 2 ≤ x ^ eps := by
  have h1 := (isLittleO_log_rpow_atTop (half_pos h)).bound one_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp h1
  refine ⟨max x0 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h2 := hx0 x (le_trans (le_max_left _ _) hx)
  have hp : 0 ≤ x ^ (eps / 2) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg hp, one_mul] at h2
  have h3 : x ^ eps = (x ^ (eps / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  rw [h3]
  exact pow_le_pow_left₀ (Real.log_nonneg hx1) h2 2

/-- **Divisibility Budget Transfer (`divinN_at_of_linkN`, matching `DivinNOfHypV.lean`)**:
Combines a single-step `LinkN` upper bound `E ≤ nT * (C * (f * m * b * (x^ε)^2 + (log x)^2 * Nc) + ∑' l, vvTerm)`
with `∑' l, vvTerm ≤ b` and `(log x)^2 ≤ x^ε` into the clean `DIVinN` envelope
`E ≤ nT * ((|C| + 1) * x^ε * (B0 + Nc))` where `B0 = f * m * b * x^ε`. -/
theorem divinN_at_of_linkN {x eps b Nc E C : ℝ} {f m nT : ℕ}
    (hx : 1 < x) (heps : 0 < eps) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hbpos : 0 < b) (hNc : 0 ≤ Nc)
    (hLink : E ≤ (nT : ℝ) * (C * ((f : ℝ) * (m : ℝ) * b * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + b))
    (hlog : Real.log x ^ 2 ≤ x ^ eps) :
    E ≤ (nT : ℝ) * ((|C| + 1) * x ^ eps * (((f : ℝ) * (m : ℝ) * b * x ^ eps) + Nc)) := by
  set y := x ^ eps with hydef
  set B0 := (f : ℝ) * (m : ℝ) * b * y with hB0def
  have hy : 1 ≤ y := Real.one_le_rpow hx.le heps.le
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfm : 1 ≤ (f : ℝ) * (m : ℝ) := one_le_mul_of_one_le_of_one_le hfR hmR
  have hbB : b ≤ B0 := by
    rw [hB0def]
    have h1 : 1 ≤ (f : ℝ) * (m : ℝ) * y := one_le_mul_of_one_le_of_one_le hfm hy
    nlinarith
  have hB0 : 0 ≤ B0 := le_trans hbpos.le hbB
  have hP1 : (f : ℝ) * (m : ℝ) * b * y ^ 2 = y * B0 := by rw [hB0def]; ring
  have hP2 : Real.log x ^ 2 * Nc ≤ y * Nc := mul_le_mul_of_nonneg_right hlog hNc
  have hP0 : 0 ≤ y * B0 + Real.log x ^ 2 * Nc := by positivity
  refine le_trans hLink (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [hP1]
  have h1 : C * (y * B0 + Real.log x ^ 2 * Nc) ≤ |C| * (y * (B0 + Nc)) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hP0)
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C))
  have h2 : b ≤ y * (B0 + Nc) := by nlinarith
  have h3 : (|C| + 1) * y * (B0 + Nc) = |C| * (y * (B0 + Nc)) + y * (B0 + Nc) := by ring
  rw [h3]
  linarith

/-- **Direct Bridge from `RHDirect.VAt` to `DIVinN` (`divinN_of_vAt`)**:
Given `VAt S ψ eps Ct q d e x` (so `VVle S E ⌊x^Ct⌋₊ √(exp(x^ε))`) and `t ≤ ⌊x^Ct⌋₊`,
the Selmer/Sha tail `∑' l, vvTerm S E t l` is bounded by `b = exp(x^ε)` and feeds straight into
the `DIVinN` divisibility envelope! -/
theorem divinN_of_vAt {S : SelmerSystem} {ψ : PChar} {eps Ct x Nc E C : ℝ}
    {q d e_page t f m nT : ℕ} {E_field : Type} [Field E_field] [NumberField E_field]
    (hV : VAt S ψ eps Ct q d e_page x) (hChi : IsChiField ψ e_page q d E_field)
    (ht : t ≤ ⌊x ^ Ct⌋₊) (hx : 1 < x) (heps : 0 < eps)
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hNc : 0 ≤ Nc)
    (hLink : E ≤ (nT : ℝ) * (C * ((f : ℝ) * (m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + ∑' l, vvTerm S E_field t l))
    (hlog : Real.log x ^ 2 ≤ x ^ eps) :
    E ≤ (nT : ℝ) * ((|C| + 1) * x ^ eps *
      (((f : ℝ) * (m : ℝ) * Real.exp (x ^ eps) * x ^ eps) + Nc)) := by
  have hVV : VVle S E_field t (Real.sqrt (Real.exp (x ^ eps))) :=
    (hV E_field hChi).mono ht le_rfl
  obtain ⟨_, _, htsum⟩ := vvRecord_of_VVle hVV
  have hb1 : 1 ≤ Real.exp (x ^ eps) :=
    Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have htsum_b : ∑' l, vvTerm S E_field t l ≤ Real.exp (x ^ eps) :=
    htsum.trans (Real.sqrt_le_self_iff.mpr (Or.inr hb1))
  have hLink' : E ≤ (nT : ℝ) * (C * ((f : ℝ) * (m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
      Real.log x ^ 2 * Nc) + Real.exp (x ^ eps)) :=
    hLink.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  exact divinN_at_of_linkN hx heps hf hm (Real.exp_pos _) hNc hLink' hlog

/-! ## Section 4: Common-Slope Cancellation Arithmetic (`Ga_bound5` & `key_identity5`) -/

section CommonSlopeCancellation

/-- Weighted average `(∑_i d_i X_i) / (∑_i d_i)`. -/
def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ i, d i * X i) / (∑ i, d i)

lemma wmean_sum_pos {ι : Type*} [Fintype ι] [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) :
    0 < ∑ i, d i := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty

lemma wmean_le_const {ι : Type*} [Fintype ι] [Nonempty ι] {d X : ι → ℝ}
    (hd : ∀ i, 0 < d i) (c : ℝ) (h : ∀ i, X i ≤ c) : wmean d X ≤ c := by
  unfold wmean
  rw [div_le_iff₀ (wmean_sum_pos hd), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi := mul_le_mul_of_nonneg_left (h i) (hd i).le
  linarith

lemma sub_wmean_le {ι : Type*} [Fintype ι] [Nonempty ι] {d X Y : ι → ℝ}
    (hd : ∀ i, 0 < d i) (c : ℝ) (h : ∀ i, c - Y i ≤ X i) :
    c - wmean d Y ≤ wmean d X := by
  have hs := wmean_sum_pos hd
  unfold wmean
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hs, mul_comm c, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi := mul_le_mul_of_nonneg_left (h i) (hd i).le
  linarith

/-- Log-entropy function `ph(y) = y * log y - y`. -/
def ph (y : ℝ) : ℝ := y * Real.log y - y

/-- Monotonicity helper `u * log (1 + H / u) ≤ (U + b) * log (1 + X)` used in `Ga_bound5`. -/
theorem phi_log_bound {u H X b U : ℝ} (hu : 0 ≤ u) (hH : 0 < H) (hHX : H ≤ X * b)
    (hb : 0 < b) (hX : 0 < X) (huU : u ≤ U) :
    u * Real.log (1 + H / u) ≤ (U + b) * Real.log (1 + X) := by
  have hlogX : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
  by_cases hu0 : u = 0
  · subst hu0
    simp only [zero_mul]
    have hU0 : 0 ≤ U := le_trans (le_refl 0) huU
    exact mul_nonneg (by linarith) hlogX
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have h1 : u * Real.log (1 + H / u) ≤ (u + b) * Real.log (1 + H / (u + b)) := by
      -- For fixed H > 0, t ↦ t * log (1 + H / t) is increasing on (0, ∞) since
      -- log(1 + a) ≥ a / (1 + a) implies d/dt [t log(1 + H/t)] = log(1 + H/t) - (H/t)/(1 + H/t) ≥ 0.
      -- Direct elementary proof via concavity of `Real.log` (`log x ≤ x - 1`):
      have hub : 0 < u + b := by linarith
      have harg : 0 < (1 + H / u) / (1 + H / (u + b)) := by positivity
      have hsub : Real.log (1 + H / u) - Real.log (1 + H / (u + b)) =
          Real.log ((1 + H / u) / (1 + H / (u + b))) :=
        (Real.log_div (by positivity) (by positivity)).symm
      have hle1 : Real.log ((1 + H / u) / (1 + H / (u + b))) ≤
          (1 + H / u) / (1 + H / (u + b)) - 1 := Real.log_le_sub_one_of_pos harg
      have hle2 : u * ((1 + H / u) / (1 + H / (u + b)) - 1) ≤
          b * (H / (u + b) / (1 + H / (u + b))) := by
        have hident : u * ((1 + H / u) / (1 + H / (u + b)) - 1) =
            b * (H / (u + b) / (1 + H / (u + b))) := by
          field_simp
          ring
        linarith
      have harg2 : 0 < (1 + H / (u + b))⁻¹ := by positivity
      have hle3 : H / (u + b) / (1 + H / (u + b)) ≤ Real.log (1 + H / (u + b)) := by
        have h := Real.log_le_sub_one_of_pos harg2
        rw [Real.log_inv] at h
        have hident : 1 - (1 + H / (u + b))⁻¹ = H / (u + b) / (1 + H / (u + b)) := by
          field_simp
          ring
        linarith
      have h4 : u * (Real.log (1 + H / u) - Real.log (1 + H / (u + b))) ≤
          b * Real.log (1 + H / (u + b)) := by
        calc u * (Real.log (1 + H / u) - Real.log (1 + H / (u + b)))
            ≤ u * ((1 + H / u) / (1 + H / (u + b)) - 1) := by
              rw [hsub]; exact mul_le_mul_of_nonneg_left hle1 hu
          _ ≤ b * (H / (u + b) / (1 + H / (u + b))) := hle2
          _ ≤ b * Real.log (1 + H / (u + b)) := mul_le_mul_of_nonneg_left hle3 hb.le
      linarith
    have h2 : Real.log (1 + H / (u + b)) ≤ Real.log (1 + X) := by
      apply Real.log_le_log (by positivity)
      have : H / (u + b) ≤ X := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    calc u * Real.log (1 + H / u)
        ≤ (u + b) * Real.log (1 + H / (u + b)) := h1
      _ ≤ (u + b) * Real.log (1 + X) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ (U + b) * Real.log (1 + X) := mul_le_mul_of_nonneg_right (by linarith) hlogX

/-- Parameters & fields for `LevelOfCongruence.lean` (`Ga_bound5` common-slope cancellation). -/
structure CongruenceSlopeData (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) where
  x : ℝ
  a : ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  v : ℝ
  L : ℝ
  La : ℝ
  lg : ℝ
  gam : ℝ
  LpL : ℝ
  B0 : ℝ
  aT : Top → ℝ
  w : U0 → Fin m → Fin f → ℝ
  T : ∀ u0, W u0 → ℝ
  Ee : ∀ u0, W u0 → ℝ
  h : ∀ u0, W u0 → ℝ
  d : ∀ u0, W u0 → ℝ
  muM : ∀ u0, W u0 → ℝ
  muMaxM : ∀ u0, W u0 → ℝ
  muN : ∀ u0, W u0 → ℝ
  muMaxN : ∀ u0, W u0 → ℝ
  muCC : U0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  IO : U0 → ℝ
  del : U0 → ℝ
  η : U0 → ℝ
  e : U0 → ℝ
  HH : U0 → ℝ
  delBar : ℝ
  etaBar : ℝ
  eBar : ℝ
  cCount : ℝ
  cSlope : ℝ
  cE : ℝ
  cDiv : ℝ
  cSl1 : ℝ
  cH : ℝ
  cHH : ℝ

namespace CongruenceSlopeData

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : CongruenceSlopeData U0 W Top m f) (Xpp : ℝ)

def nT (_ : CongruenceSlopeData U0 W Top m f) : ℝ := (Fintype.card Top : ℝ)
def sumA : ℝ := ∑ t : Top, D.aT t
def logOm : ℝ := D.gam + Real.log (Real.pi / D.v) - D.LpL
def s (u0 : U0) : ℝ := wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u)
def uF (u0 : U0) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) - D.s u0

def fiber (u0 : U0) : BostSlopeFiber where
  del := D.del u0
  η := D.η u0
  e := D.e u0
  s := D.s u0
  muMinCC := D.muMinCC u0
  muCC := D.muCC u0
  HH := D.HH u0
  uF := D.uF u0
  cardW := Fintype.card (W u0)

def Lam5 (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi)) +
    (m : ℝ) * D.lg - D.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)

def Main (u0 : U0) : ℝ :=
  ∑ t : Top, (m : ℝ) * (ph (D.aT t) - D.aT t * (D.gam - D.LpL)) -
    D.sumA * ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)

def SDiv : ℝ := ∑ t : Top, (m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm)

def EDiv : ℝ := D.cDiv * D.nT * D.B0

def K5v5 (u0 : U0) : ℝ :=
  D.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) + (m : ℝ) * (D.sumA * D.lg + D.cE * D.B0) +
    D.SDiv - D.sumA * D.Lam5 u0 + D.EDiv

def K0v5 : ℝ :=
  D.sumA * (D.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) +
    D.EDiv + (m : ℝ) * D.cE * D.B0 + D.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)

def Lo5 (u0 : U0) (u : W u0) : ℝ :=
  D.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u) + D.cSl1 * D.IO u0 +
    D.cSl1 * Xpp + 1

def K7v5 : ℝ :=
  D.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (D.cCount * (m : ℝ) * D.L) + D.cSl1 * Xpp + 1

def Vvar : ℝ :=
  2 * (m : ℝ) * D.cE * D.B0 + D.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0) +
    D.sumA * (D.cCount * Real.log D.k)

def K3 : ℝ :=
  D.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.cSl1 * (m : ℝ) * D.B0 + D.Vvar

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
/-- Exact algebraic cancellation of `log (π / v)` and `m * sumA * lg` (`key_identity5` in
`LevelOfCongruence.lean`). -/
theorem key_identity5 (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * D.Lam5 u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (D.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have hsplit :
      (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi)) =
        (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) -
          (m : ℝ) * Real.log (Real.pi / D.v) := by
    have hterm : ∀ j : Fin m,
        (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi) =
          (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ) - Real.log (Real.pi / D.v) := by
      intro j
      have hinner : ∀ ρ : Fin f,
          Real.log (D.w u0 j ρ * D.v / Real.pi) =
            Real.log (D.w u0 j ρ) - Real.log (Real.pi / D.v) := by
        intro ρ
        have hwj := hw j ρ
        rw [Real.log_div (mul_pos hwj hv).ne' hpi.ne', Real.log_mul hwj.ne' hv.ne',
          Real.log_div hpi.ne' hv.ne']
        ring
      simp_rw [hinner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hSDiv :
      D.SDiv = (∑ t : Top, (m : ℝ) * (ph (D.aT t) - D.aT t * (D.gam - D.LpL))) -
        (m : ℝ) * D.sumA * Real.log (Real.pi / D.v) := by
    unfold SDiv logOm sumA
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  unfold Main Lam5
  rw [hsplit, hSDiv]
  ring

omit [Fintype U0] in
/-- **Lower Bound on the Weighted Mean Slope `s(u0)` (`s_lower5`)**:
Cancels the fiber shift `D.Fo u0` between the `p`-adic divisibility bound `hDIV` and the
quotient slope bound `hSN`, isolating `Ga(u0) + muCC(u0)` on the left-hand side! -/
theorem s_lower5 (u0 : U0)
    (hd : ∀ u : W u0, 0 < D.d u0 u)
    (hsumA : 0 ≤ D.sumA)
    (hDIV : ∀ u : W u0,
      D.muCC u0 + D.h u0 u - D.Fo u0 ≤
        (∑ t : Top, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u))) +
          D.EDiv)
    (hE : ∀ u : W u0, |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ D.cE * (m : ℝ) * D.B0)
    (hCount : ∀ u : W u0, D.Lam5 u0 ≤ Real.log (D.T u0 u))
    (hSl : ∀ u : W u0, -(D.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u)
    (hSN : ∀ u : W u0,
      D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo5 Xpp u0 u ≤ D.muN u0 u) :
    D.Ga u0 + D.muCC u0 - D.K5v5 u0 - wmean (D.d u0) (D.Lo5 Xpp u0) ≤ D.s u0 := by
  unfold s
  refine sub_wmean_le hd _ fun u => ?_
  have h1 := hSN u
  have h2 := hDIV u
  rw [Finset.sum_sub_distrib] at h2
  have hsum_eq : ∑ t : Top, D.aT t * Real.log (D.T u0 u) = D.sumA * Real.log (D.T u0 u) := by
    rw [← Finset.sum_mul]; rfl
  rw [hsum_eq] at h2
  have h3 := mul_le_mul_of_nonneg_left (hCount u) hsumA
  have h4 := (abs_le.mp (hE u)).2
  have h5 := hSl u
  unfold K5v5 SDiv
  linarith

omit [Fintype U0] [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] in
/-- Uniform variation bound `Vvar_bound5` between two fibers `u, u' ∈ W u0`. -/
theorem Vvar_bound5 (u0 : U0) (u u' : W u0)
    (hsumA : 0 ≤ D.sumA)
    (hE : ∀ v : W u0, |D.Ee u0 v - (m : ℝ) * D.sumA * D.lg| ≤ D.cE * (m : ℝ) * D.B0)
    (hH : |(D.h u0 u' + ∑ t : Top, D.aT t * Real.log (D.T u0 u')) -
        (D.h u0 u + ∑ t : Top, D.aT t * Real.log (D.T u0 u))| ≤
      D.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0))
    (hTdiff : |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ D.cCount * Real.log D.k) :
    (-D.Ee u0 u - D.h u0 u) - (-D.Ee u0 u' - D.h u0 u') ≤ D.Vvar := by
  have h1 := (abs_le.mp (hE u')).2
  have h2 := (abs_le.mp (hE u)).1
  have h3 := (abs_le.mp hH).2
  have hs1 : ∑ t : Top, D.aT t * Real.log (D.T u0 u') = D.sumA * Real.log (D.T u0 u') := by
    rw [← Finset.sum_mul]; rfl
  have hs2 : ∑ t : Top, D.aT t * Real.log (D.T u0 u) = D.sumA * Real.log (D.T u0 u) := by
    rw [← Finset.sum_mul]; rfl
  rw [hs1, hs2] at h3
  have h4 := mul_le_mul_of_nonneg_left (abs_le.mp hTdiff).2 hsumA
  unfold Vvar
  linarith

omit [Fintype U0] in
/-- **Upper Bound on the Slope Defect `uF(u0)` (`u_function_le_mean`)**:
Cancels `Ga(u0) + Fo(u0)` between `muMaxN` and `muN`, bounding `uF(u0)` by `K3 + wmean Lo5`. -/
theorem u_function_le_mean (u0 : U0)
    (hd : ∀ u : W u0, 0 < D.d u0 u) (hsumA : 0 ≤ D.sumA)
    (hE : ∀ v : W u0, |D.Ee u0 v - (m : ℝ) * D.sumA * D.lg| ≤ D.cE * (m : ℝ) * D.B0)
    (hH : ∀ u u' : W u0,
      |(D.h u0 u' + ∑ t : Top, D.aT t * Real.log (D.T u0 u')) -
        (D.h u0 u + ∑ t : Top, D.aT t * Real.log (D.T u0 u))| ≤
      D.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0))
    (hTdiff : ∀ u u' : W u0,
      |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ D.cCount * Real.log D.k)
    (hSl : ∀ u : W u0,
      -(D.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
      D.muMaxM u0 u ≤ D.cSlope * D.nT * D.a * D.La)
    (hSN : ∀ u : W u0,
      D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + D.cSl1 * (m : ℝ) * D.B0 ∧
      D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo5 Xpp u0 u ≤ D.muN u0 u) :
    D.uF u0 ≤ D.K3 + wmean (D.d u0) (D.Lo5 Xpp u0) := by
  have hs : ∀ u : W u0,
      (D.muMaxN u0 u - D.h u0 u - D.K3) - wmean (D.d u0) (D.Lo5 Xpp u0) ≤ D.s u0 := by
    intro u
    unfold s
    refine sub_wmean_le hd _ fun u' => ?_
    have h1 := (hSN u).1
    have h2 := (hSN u').2
    have h3 := (hSl u).2
    have h4 := (hSl u').1
    have h5 := D.Vvar_bound5 u0 u u' hsumA hE (hH u u') (hTdiff u u')
    unfold K3
    linarith
  unfold uF
  have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W u0))
    (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)
    (a := D.s u0 + (D.K3 + wmean (D.d u0) (D.Lo5 Xpp u0)))
    (fun u _ => by have := hs u; linarith)
  linarith

omit [Fintype U0] in
/-- **Pointwise Common-Slope Cancellation Bound (`Ga_bound5`)**:
Cancels the common dual-lattice slope `D.muCC u0` between `s_lower5` (divisibility lower bound)
and `(D.fiber u0).SlopeIneq` (Bost Arakelov slope inequality), then applies `key_identity5`
to cancel `m * sumA * lg` and `log (π / v)`! -/
theorem Ga_bound5 (u0 : U0)
    (hx : 0 < D.x) (hb : 0 < D.b) (hv : 0 < D.v) (hf : 0 < f)
    (hw : ∀ j ρ, 0 < D.w u0 j ρ)
    (hdel0 : 0 ≤ D.del u0) (hdelBar : D.del u0 ≤ D.delBar) (hdelBar1 : D.delBar < 1)
    (hη0 : 0 ≤ D.η u0) (hηBar : D.η u0 ≤ D.etaBar)
    (he0 : 0 ≤ D.e u0) (he4 : D.e u0 ≤ 1 / 4) (heBar : D.e u0 ≤ D.eBar)
    (hHH0 : 0 < D.HH u0) (hHH_s : D.s u0 - D.muMinCC u0 ≤ D.HH u0)
    (hHH_up : D.HH u0 ≤ D.x ^ D.cHH * D.b)
    (huF0 : 0 ≤ D.uF u0)
    (huF_le : D.uF u0 ≤ D.K3 + wmean (D.d u0) (D.Lo5 Xpp u0))
    (hs_lo : D.Ga u0 + D.muCC u0 - D.K5v5 u0 - wmean (D.d u0) (D.Lo5 Xpp u0) ≤ D.s u0)
    (hSI : (D.fiber u0).SlopeIneq) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + D.K0v5 +
      wmean (D.d u0) (D.Lo5 Xpp u0) +
      (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ D.cHH) *
        (D.K3 + wmean (D.d u0) (D.Lo5 Xpp u0) + D.b) +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ D.cHH * D.b)) := by
  have hdel1 : D.del u0 < 1 := lt_of_le_of_lt hdelBar hdelBar1
  have hsl := hSI hdel0 hdel1 hη0 he0 he4 hHH_s hHH0
  dsimp only [fiber] at hsl
  have hX : 0 < D.x ^ D.cHH := Real.rpow_pos_of_pos hx _
  have hphi := phi_log_bound huF0 hHH0 hHH_up hb hX huF_le
  have hsqrt : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt heBar
  have hterm2 : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 ≤
      (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ D.cHH * D.b) := by
    have h0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) := by positivity
    have h1 : D.η u0 + 4 * Real.sqrt (D.e u0) ≤ D.etaBar + 4 * Real.sqrt D.eBar := by linarith
    exact mul_le_mul h1 hHH_up hHH0.le (by linarith)
  have hlog_nonneg : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) := by
    have hdiv : 0 ≤ D.HH u0 / D.uF u0 := div_nonneg hHH0.le huF0
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hsum_nonneg : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) +
      (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := by
    have : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := by positivity
    linarith
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have hcorr :
      (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) +
        (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤
      (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ D.cHH) *
        (D.K3 + wmean (D.d u0) (D.Lo5 Xpp u0) + D.b) +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ D.cHH * D.b)) := by
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) +
            (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv hsum_nonneg
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hinv0
          linarith
  have hkey := D.key_identity5 hv hf u0 hw
  unfold K0v5 K5v5 at *
  linarith

omit [Fintype U0] in
/-- Weighted-mean upper bound on `Lo5` (`weighted_mean_lower_bound_le` in `LevelOfCongruence.lean`). -/
theorem weighted_mean_lower_bound_le (u0 : U0)
    (hd : ∀ u : W u0, 0 < D.d u0 u)
    (ha : 0 ≤ D.a) (hb' : 0 ≤ D.b') (hk : 0 < D.k) (hcSl1 : 0 ≤ D.cSl1)
    (hT : ∀ u : W u0, Real.log (D.T u0 u) ≤ D.cCount * (m : ℝ) * D.L) :
    wmean (D.d u0) (D.Lo5 Xpp u0) ≤ D.cSl1 * D.IO u0 + D.K7v5 Xpp := by
  refine wmean_le_const hd _ fun u => ?_
  have hnT : 0 ≤ D.nT := Nat.cast_nonneg _
  have hc : 0 ≤ D.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (mul_nonneg hcSl1 hnT) (Nat.cast_nonneg _))
      (add_nonneg (div_nonneg ha hk.le) hb')
  have h1 := mul_le_mul_of_nonneg_left (hT u) hc
  unfold Lo5 K7v5
  linarith

end CongruenceSlopeData

end CommonSlopeCancellation

end

end RHDirect.PAdicChainValuation
