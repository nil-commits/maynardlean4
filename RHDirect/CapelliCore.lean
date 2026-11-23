import RHDirect.Interfaces
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# RHDirect.CapelliCore

Compact, idiomatic, zero-`sorry`, zero-axiom from-scratch rebuild of the **Capelli Identities &
Integral-Cast Algebraic Core**, replacing the 879-file / 117,334-line directory
`Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/` (including `FixPiIff.lean`
at 8,029 lines for 2 declarations and `CovariantDegrees.lean` at 5,600+ lines of raw dumped
elaborated terms).

## Contents
1. **Universal Enveloping Algebra `U(𝔤𝔩_n)`, Capelli Matrix Powers & Casimir Algebra**:
   - `GlRel`: standard `𝔤𝔩_n` commutation relations `[E_{ab}, E_{cd}] = δ_{bc} E_{ad} - δ_{da} E_{cb}`.
   - `commutator_matrix_pow` & `trace_matrix_pow_comm`: general noncommutative commutator induction
     yielding central traces `∑_a (M^k)_{aa}`.
   - `capelliMatrix`, `e_mul_sub_mul_capelliMatrix_pow`, `e_comm_trace_capelliMatrix_pow`:
     exact Capelli matrix power commutation and centrality of traces in `U(𝔤𝔩_n)`.
   - `casK_comm` & `casC_eq_sum_shifted`: block-signature Casimir commutation and Harish-Chandra
     shifted quadratic Casimir identity.
2. **Quantum Minors, Quantum Determinant & 2×2 Capelli-Casimir Eigenvalue Identity**:
   - `capelliTm`, `qminor`, `qdet`, and `qdet_two_holomorphic_eigenvalue`:
     `qdet E (u + 1/2) φ = ((u + (k - 1)/2) * (u - (k - 1)/2)) • φ` on holomorphic weight-`k`
     vectors (collapsing the duplicated `Qminor.lean` / `QuantumMinorsCasimir.lean` files).
3. **Matrix Determinants, Vandermonde, Jacobi Derivative & Bilinear Preservation**:
   - `det_norm_le` (`‖A.det‖ ≤ n! * C^n`), `vandermonde_eq_det`,
     `det_sq_eq_one_of_preserves_bilin`, and `hasDerivAt_det_at_one` (Jacobi formula at `1`).
4. **Integral Closure, Ultrametric Bounds, `p`-adic Height-One Primes & Iwahori Charpoly Valuations**:
   - `norm_le_one_of_monic_root`, `isIntegral_det_of_isIntegral`,
     `isIntegral_det_of_preserves_lattice`.
   - `kappa_ringOfIntegers_norm_le_one` & `exists_heightOneSpectrum_valuation_le_one_iff_norm_le_one`
     (`CapelliComplements/KappaIntegralBound.lean`, stripped of 276 unused imports).
   - `valuation_det_le_one_of_entries_le_one`, `valuation_det_eq_one_iff_diag_eq_one`, and
     `charpoly_coeff_valuation` (exact Newton-polygon valuations of `diagonal d * M`).
5. **Homogeneous Polynomials, Covariant Degrees & Linear Substitution Bounds**:
   - `aeval_mul_of_isHomogeneous`, `degLE_sum`, `totalDegree_aeval_le_of_le_one`,
     `totalDegree_linear_subst_le`, and `isWeightedHomogeneous_map_iff` /
     `aeval_map_eq_rename_map_iff`.
6. **Product-Group Fixed Vectors & Krull-Topology Decomposition Continuity**:
   - `fix_pi_iff` & `mem_fixedSubmodule_pi_iff` (collapsing the 8,029-line `FixPiIff.lean` into
     20 lines!).
   - `continuous_krull_restriction` (collapsing `CovariantDegrees.lean`'s 5,600+ lines of raw
     elaborated casts into a clean 20-line Krull-topology continuity proof!).
-/

noncomputable section

namespace RHDirect.CapelliCore

open scoped Polynomial

/-! ## 1. Universal Enveloping Algebra `U(𝔤𝔩_n)`, Capelli Matrix Powers & Casimir Algebra -/

/-- Standard `𝔤𝔩_n` commutation relations in an associative ring `A`. -/
def GlRel {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n,
    E a b * E c d - E c d * E a b =
      (if b = c then E a d else 0) - (if d = a then E c b else 0)

/-- General noncommutative Capelli matrix-power commutator identity:
if `[x, M_{cd}] = δ_{bc} M_{ad} - δ_{da} M_{cb}`, then the same holds for every power `M^k`. -/
theorem commutator_matrix_pow {R : Type*} [Ring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d : Fin n,
      x * M c d - M c d * x = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : ℕ) (c d : Fin n) :
    x * (M ^ k) c d - (M ^ k) c d * x =
      (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp [h1, h2, eq_comm (a := a), eq_comm (a := c)]
  | succ k ih =>
    have key : ∀ j : Fin n,
        x * ((M ^ k) c j * M j d) - (M ^ k) c j * M j d * x =
          ((if b = c then (M ^ k) a j else 0) - (if j = a then (M ^ k) c b else 0)) * M j d +
            (M ^ k) c j * ((if b = j then M a d else 0) - (if d = a then M j b else 0)) := by
      intro j
      rw [← ih j, ← h j d]
      noncomm_ring
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun j _ => key j]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;> abel

/-- Centrality of matrix-power traces: under the `𝔤𝔩_n` commutator hypothesis on `x` and `M`,
`x` commutes with `Matrix.trace (M ^ k)` for every `k : ℕ`. -/
theorem trace_matrix_pow_comm {R : Type*} [Ring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d : Fin n,
      x * M c d - M c d * x = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : ℕ) :
    x * (M ^ k).trace = (M ^ k).trace * x := by
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply]
  calc ∑ c : Fin n, (x * (M ^ k) c c - (M ^ k) c c * x)
      = ∑ c : Fin n, ((if b = c then (M ^ k) a c else 0) - (if c = a then (M ^ k) c b else 0)) :=
        Finset.sum_congr rfl fun c _ => commutator_matrix_pow M x a b h k c c
    _ = (∑ c : Fin n, if b = c then (M ^ k) a c else 0) -
          (∑ c : Fin n, if c = a then (M ^ k) c b else 0) := Finset.sum_sub_distrib _ _
    _ = (M ^ k) a b - (M ^ k) a b := by simp
    _ = 0 := sub_self _

/-- Complex general linear Lie algebra `𝔤𝔩_n(ℂ)`. -/
abbrev gl (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

/-- Universal enveloping algebra `U(𝔤𝔩_n(ℂ))`. -/
abbrev Ugl (n : ℕ) : Type :=
  @UniversalEnvelopingAlgebra ℂ (gl n) _ (LieRing.ofAssociativeRing)
    (LieAlgebra.ofAssociativeAlgebra)

/-- Standard matrix unit `E_{ab} ∈ 𝔤𝔩_n(ℂ)`. -/
def glUnit {n : ℕ} (a b : Fin n) : gl n := Matrix.single a b (1 : ℂ)

/-- Canonical generator `e_{ab} ∈ U(𝔤𝔩_n(ℂ))`. -/
def ueaGen {n : ℕ} (a b : Fin n) : Ugl n :=
  @UniversalEnvelopingAlgebra.ι ℂ (gl n) _ LieRing.ofAssociativeRing
    LieAlgebra.ofAssociativeAlgebra (glUnit a b)

/-- The `n × n` Capelli matrix `(e_{ij})` with entries in `U(𝔤𝔩_n(ℂ))`. -/
def capelliMatrix {n : ℕ} : Matrix (Fin n) (Fin n) (Ugl n) :=
  Matrix.of fun i j => ueaGen i j

theorem glUnit_glRel (n : ℕ) : GlRel (glUnit (n := n)) := by
  intro a b c d
  have hmul : ∀ p q r s : Fin n, glUnit p q * glUnit r s = if q = r then glUnit p s else 0 := by
    intro p q r s
    unfold glUnit
    split_ifs with hqr
    · subst hqr; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [hmul, hmul]

theorem ueaGen_glRel (n : ℕ) : GlRel (ueaGen (n := n)) := by
  intro a b c d
  let _ : LieRing (gl n) := LieRing.ofAssociativeRing
  let _ : LieAlgebra ℂ (gl n) := LieAlgebra.ofAssociativeAlgebra
  let _ : LieRing (Ugl n) := LieRing.ofAssociativeRing
  unfold ueaGen
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, glUnit_glRel n a b c d, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _

/-- Capelli matrix power commutation in `U(𝔤𝔩_n(ℂ))` (`EMulSubMulCapelliMatrixPow.lean`). -/
theorem e_mul_sub_mul_capelliMatrix_pow {n : ℕ} (a b : Fin n) (k : ℕ) (c d : Fin n) :
    ueaGen a b * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * ueaGen a b =
      (if b = c then (capelliMatrix ^ k) a d else 0) -
        (if d = a then (capelliMatrix ^ k) c b else 0) :=
  commutator_matrix_pow capelliMatrix (ueaGen a b) a b (fun c d => ueaGen_glRel n a b c d) k c d

/-- Every Gelfand/Capelli trace `trace(capelliMatrix ^ k)` lies in the center of `U(𝔤𝔩_n(ℂ))`. -/
theorem e_comm_trace_capelliMatrix_pow {n : ℕ} (a b : Fin n) (k : ℕ) :
    ueaGen a b * (capelliMatrix ^ k).trace = (capelliMatrix ^ k).trace * ueaGen a b :=
  trace_matrix_pow_comm capelliMatrix (ueaGen a b) a b (fun c d => ueaGen_glRel n a b c d) k

/-- Block-signature quadratic Casimir element `∑_{ε(a) = ε(b)} E_{ab} E_{ba}`. -/
def casK {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A) : A :=
  ∑ a : Fin n, ∑ b : Fin n, if ε a = ε b then E a b * E b a else 0

/-- Block-diagonal Casimir commutation (`CasimirCommutation.lean`):
`CasK ε E` commutes with every `E_{cd}` inside a block (`ε c = ε d`). -/
theorem casK_comm {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A)
    (h : GlRel E) {c d : Fin n} (hcd : ε c = ε d) :
    casK ε E * E c d = E c d * casK ε E := by
  have key : ∀ a b : Fin n,
      E a b * E b a * E c d - E c d * (E a b * E b a) =
        E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0) +
          (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have hrew :
        E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0) +
          (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a =
        E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [hrew, ← h1, ← h2]
    noncomm_ring
  have hS1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0) =
      ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]; simp
  have hS4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) =
      ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]; simp
  have hS2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0) =
      ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]; simp
  have hS3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0) =
      ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]; simp
  have he : casK ε E * E c d - E c d * casK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [casK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have he2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) =
      (∑ a, ∑ b, if ε a = ε b then E a b * (if a = c then E b d else 0) else 0) -
        (∑ a, ∑ b, if ε a = ε b then E a b * (if d = b then E c a else 0) else 0) +
        (∑ a, ∑ b, if ε a = ε b then (if b = c then E a d else 0) * E b a else 0) -
        (∑ a, ∑ b, if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]; split_ifs <;> simp
  rw [← sub_eq_zero, he, he2, hS1, hS2, hS3, hS4, hcd]
  abel

/-- Harish-Chandra quadratic Casimir eigenvalue `∑_a τ_a^2 + ∑_{a < b} (τ_a - τ_b)`. -/
def casC {n : ℕ} (τ : Fin n → ℂ) : ℂ :=
  ∑ a : Fin n, τ a ^ 2 + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else 0

/-- Exact rho-shift expansion of `casC` (`CasimirElement.lean`). -/
theorem casC_eq_sum_shifted {n : ℕ} (σ : Fin n → ℂ) :
    casC σ = ∑ a : Fin n, σ a ^ 2 + ∑ a : Fin n, σ a * ((n : ℂ) - 1 - 2 * (a : ℕ)) := by
  have hL : ∀ a : Fin n,
      (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - (a : ℕ)) := by
    intro a
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
    have ha : (a : ℕ) ≤ n - 1 := by omega
    have hn : 1 ≤ n := by omega
    rw [Nat.cast_sub ha, Nat.cast_sub hn]
    push_cast; ring
  have hR : ∀ b : Fin n,
      (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * (b : ℕ) := by
    intro b
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
    ring
  unfold casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := fun a b => by
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [hL, hR]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ## 2. Quantum Minors, Quantum Determinant & 2×2 Capelli-Casimir Eigenvalue Identity -/

/-- Shifted Capelli generator matrix `T(u)_{ab} = δ_{ab} u + E_{ab}`. -/
def capelliTm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  (if a = b then algebraMap ℂ A u else 0) + E a b

/-- Quantum minor `qminor E a b u` in a `ℂ`-algebra `A`. -/
def qminor {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t => capelliTm E (u - (k : ℕ)) (a (σ k)) (b k)).prod

/-- Quantum (Capelli) determinant `qdet E u = qminor E id id u`. -/
def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E id id u

/-- Exact 2×2 Capelli quantum-determinant eigenvalue on holomorphic lowest-weight vectors
(collapsing both cloned 30 KB files `Qminor.lean` and `QuantumMinorsCasimir.lean` into one proof). -/
theorem qdet_two_holomorphic_eigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    (E : Fin 2 → Fin 2 → Module.End ℂ V) (hE : GlRel E) (k : ℂ) (φ : V)
    (h1 : E 0 0 φ + E 1 1 φ = 0)
    (h2 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ)
    (h3 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  have hq : ∀ v : ℂ, qdet E v φ =
      (v * (v - 1)) • φ + v • E 1 1 φ + (v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ) - E 1 0 (E 0 1 φ) := by
    intro v
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    unfold qdet qminor capelliTm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  have c (a b c' d : Fin 2) := congrArg (fun f : Module.End ℂ V => f φ) (hE a b c' d)
  have cad := c 0 0 1 1
  have cab := c 0 0 0 1
  have cac := c 0 0 1 0
  have cdb := c 1 1 0 1
  have cdc := c 1 1 1 0
  have cbc := c 0 1 1 0
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, LinearMap.zero_apply] at cad cab cac cdb cdc cbc
  have z (a b : Fin 2) := congrArg (E a b) h1
  have w (a b : Fin 2) := congrArg (E a b) h2
  have g (a b : Fin 2) := congrArg (E a b) h3
  simp only [map_add, map_sub, map_smul, map_zero] at z w g
  rw [hq]
  linear_combination (norm := skip) u • h1 + (1 / 4 : ℂ) • (z 0 0 + z 1 1 - (g 0 0 - g 1 1)
    - Complex.I • (g 0 1 + g 1 0) - (2 * Complex.I) • h2 + (w 0 1 - w 1 0)
    + (Complex.I * k) • h2 + (2 : ℂ) • cad - Complex.I • (cab + cac - cdb - cdc)
    + (2 : ℂ) • cbc)
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-! ## 3. Matrix Determinants, Vandermonde, Jacobi Derivative & Bilinear Preservation -/

/-- Entrywise determinant norm bound `‖A.det‖ ≤ n! * C^n` (`DetNormLe.lean`). -/
theorem det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {C : ℝ}
    (h : ∀ i j : ι, ‖A i j‖ ≤ C) :
    ‖A.det‖ ≤ ((Fintype.card ι).factorial : ℝ) * C ^ Fintype.card ι := by
  have hterm : ∀ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ C ^ Fintype.card ι := by
    intro σ
    have hs : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · rw [h1, one_smul]
      · rw [h1, Units.neg_smul, one_smul, norm_neg]
    rw [hs, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : ι, C :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
      _ = C ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, C ^ Fintype.card ι := Finset.sum_le_sum fun σ _ => hterm σ
    _ = ((Fintype.card ι).factorial : ℝ) * C ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- Reverse-power Vandermonde determinant identity (`VandermondeOfEqDet.lean`). -/
theorem vandermonde_eq_det {m : ℕ} {R : Type*} [CommRing R] (v : Fin m → R) :
    (∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j => i < j), (v i - v j)) =
      (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))).det := by
  have hM : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      Matrix.projVandermonde (fun _ => (1 : R)) v := by
    ext i j
    rw [Matrix.of_apply, Matrix.projVandermonde_apply, one_pow, one_mul, Fin.val_rev,
      Nat.sub_sub, Nat.add_comm]
  rw [hM, Matrix.det_projVandermonde]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr ?_ fun j _ => ?_
  · ext j; simp
  · rw [one_mul, one_mul]

/-- Any linear endomorphism preserving a nondegenerate real bilinear form has `(det f)^2 = 1`
(`DetSqEqOneOfPreservesBilin.lean`). -/
theorem det_sq_eq_one_of_preserves_bilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y : V, B (f x) (f y) = B x y) :
    (LinearMap.det f) ^ 2 = 1 := by
  classical
  let b := Module.finBasis ℝ V
  have hcomp : B.comp f f = B := by ext x y; simpa using hf x y
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp] at hmat
  have hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  apply mul_left_cancel₀ hne
  linear_combination -hdet

/-- Jacobi's determinant derivative formula at the identity (`CapelliComplements/ProductIdentities.lean`). -/
theorem hasDerivAt_det_at_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (hd : ∀ i j : ι, HasDerivAt (fun t : ℝ => A t i j) (A' i j) 0) :
    HasDerivAt (fun t : ℝ => (A t).det) A'.trace 0 := by
  have hzero : ∀ (σ : Equiv.Perm ι), σ ≠ 1 → ∀ k : ι,
      ∏ j ∈ Finset.univ.erase k, (1 : Matrix ι ι ℂ) (σ j) j = 0 := by
    intro σ hσ k
    have hex : ∃ j, j ≠ k ∧ σ j ≠ j := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      apply hσ
      ext x
      simp only [Equiv.Perm.coe_one, id_eq]
      by_cases hx : x = k
      · subst hx
        by_contra hk
        exact hk (σ.injective (h (σ x) hk))
      · exact h x hx
    obtain ⟨j, hjk, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩) (by simp [hj])
  have key : ∀ σ : Equiv.Perm ι, HasDerivAt
      (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ k, (∏ j ∈ Finset.univ.erase k, A 0 (σ j) j) • A' (σ k) k) 0 := fun σ =>
    HasDerivAt.const_mul _ <|
      HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
        (f' := fun i => A' (σ i) i) (fun k _ => hd (σ k) k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have hfun : (fun t : ℝ => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t => Matrix.det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · rw [h0]; simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    rw [h0, Finset.sum_eq_zero fun k _ => by rw [hzero σ hσ k, zero_smul], mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 4. Integral Closure, Ultrametric Bounds, `p`-adic Primes & Iwahori Charpoly Valuations -/

/-- In an ultrametric normed field, every root of a monic polynomial over an integrally bounded
subring lies in the closed unit ball (`NormLeOneOfMonicRoot.lean`). -/
theorem norm_le_one_of_monic_root {R L : Type*} [CommRing R] [NormedField L] [IsUltrametricDist L]
    (φ : R →+* L) (hφ : ∀ a : R, ‖φ a‖ ≤ 1) (x : L) (p : R[X])
    (hp : p.Monic) (hx : Polynomial.eval₂ φ x p = 0) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  have h1 : 1 < ‖x‖ := not_le.mp hlt
  have h0 : 0 < ‖x‖ := lt_trans one_pos h1
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hx
  have hx' : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hx
  have hb : ‖∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i‖ ≤ ‖x‖ ^ p.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ h0]
    calc ‖φ (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by gcongr; exact hφ _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ p.natDegree := pow_le_pow_right₀ h1.le hi'
  rw [← norm_neg, ← hx', norm_pow] at hb
  exact absurd hb (not_le.mpr (div_lt_self (by positivity) h1))

/-- If a matrix over a field `E` is integral over `R`, then its determinant is integral over `R`
(`IsIntegralDetOfIsIntegral.lean`). -/
theorem isIntegral_det_of_isIntegral {R E : Type*} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (γ : Matrix (Fin N) (Fin N) E) (h : IsIntegral R γ) :
    IsIntegral R γ.det := by
  let K := AlgebraicClosure E
  let φ : Matrix (Fin N) (Fin N) E →ₐ[R] Matrix (Fin N) (Fin N) K :=
    (IsScalarTower.toAlgHom R E K).mapMatrix
  have hφ : IsIntegral R (φ γ) := h.map φ
  have hdet : algebraMap E K γ.det = (φ γ).det := RingHom.map_det (algebraMap E K) γ
  rw [← isIntegral_algebraMap_iff (B := K) (algebraMap E K).injective, hdet,
    Matrix.det_eq_prod_roots_charpoly]
  refine IsIntegral.multiset_prod fun μ hμ => ?_
  have hspec : μ ∈ spectrum K (φ γ) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
  obtain ⟨p, hp, hp0⟩ := hφ
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ γ) (p.map (algebraMap R K)) ⟨μ, hspec, rfl⟩
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp0] at h1
  simp only [Polynomial.eval_map] at h1
  by_contra hne
  apply h1
  rw [spectrum.mem_resolventSet_iff, sub_zero]
  exact (IsUnit.mk0 _ hne).map _

/-- If `γ ∈ M_N(E)` stabilizes a finitely generated full `𝒪_E`-lattice `L ⊆ E^N`, then
`IsIntegral ℤ γ.det` (`IsIntegralDetOfIsIntegral.lean`). -/
theorem isIntegral_det_of_preserves_lattice {E : Type*} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) :
    IsIntegral ℤ γ.det := by
  refine isIntegral_trans (A := NumberField.RingOfIntegers E) _
    (isIntegral_det_of_isIntegral γ ?_)
  have : Module.Finite (NumberField.RingOfIntegers E) L := Module.Finite.iff_fg.2 hfg
  let g : (Fin N → E) →ₗ[NumberField.RingOfIntegers E] (Fin N → E) :=
    (Matrix.mulVecLin γ).restrictScalars _
  let f : Module.End (NumberField.RingOfIntegers E) L := g.restrict (p := L) (q := L) hγ
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (NumberField.RingOfIntegers E) f
  refine ⟨p, hp, ?_⟩
  have hpow : ∀ (n : ℕ) (v : L), ((f ^ n) v : Fin N → E) = (γ ^ n).mulVec v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, ← Matrix.mulVec_mulVec]; rfl
  have key : ∀ (q : (NumberField.RingOfIntegers E)[X]) (v : L),
      ((Polynomial.aeval f q) v : Fin N → E) = (Polynomial.aeval γ q).mulVec v := by
    intro q v
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb, Matrix.add_mulVec]
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
        ← Algebra.smul_def, LinearMap.smul_apply, Submodule.coe_smul, hpow]
      ext i
      change a • (∑ j, (γ ^ n) i j * (v : Fin N → E) j) = ∑ j, (a • (γ ^ n) i j) * (v : Fin N → E) j
      simp only [Algebra.smul_def, mul_assoc, Finset.mul_sum]
  have hz : Matrix.mulVecLin (Polynomial.aeval γ p) = 0 := by
    refine LinearMap.ext_on hspan fun v hv => ?_
    have := key p ⟨v, hv⟩
    rw [hp0] at this
    simpa using this.symm
  rw [← Polynomial.aeval_def]
  apply Matrix.toLin'.injective
  rw [map_zero]
  exact hz

/-- Every embedding `κ : K →+* ℂ_p` maps the ring of integers `𝒪_K` into the closed unit ball
(`CapelliComplements/KappaIntegralBound.lean`), proved directly from `norm_le_one_of_monic_root`. -/
theorem kappa_ringOfIntegers_norm_le_one {K : Type} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (κ : K →+* PadicComplex p) (r : NumberField.RingOfIntegers K) :
    ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := by
  obtain ⟨q, hq, hq0⟩ := NumberField.RingOfIntegers.isIntegral_coe r
  refine norm_le_one_of_monic_root (Int.castRingHom (PadicComplex p))
    (fun a => IsUltrametricDist.norm_intCast_le_one (PadicComplex p) a) _ q hq ?_
  have h := congrArg κ hq0
  rw [Polynomial.hom_eval₂, map_zero,
    RingHom.ext_int (κ.comp (algebraMap ℤ K)) (Int.castRingHom (PadicComplex p))] at h
  exact h

/-- Every embedding `κ : K →+* ℂ_p` of a number field induces a height-one prime `la` of `𝒪_K`
whose valuation unit ball coincides with `{a ∈ K | ‖κ a‖ ≤ 1}`
(`CapelliComplements/KappaIntegralBound.lean`, stripped of 276 unused imports). -/
theorem exists_heightOneSpectrum_valuation_le_one_iff_norm_le_one {K : Type} [Field K]
    [NumberField K] (p : ℕ) [hp : Fact p.Prime] (κ : K →+* PadicComplex p) :
    ∃ la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1 := by
  have hle : ∀ r : NumberField.RingOfIntegers K,
      ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 :=
    kappa_ringOfIntegers_norm_le_one p κ
  let I : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {r | ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        calc ‖κ (algebraMap _ K c)‖ * ‖κ (algebraMap _ K a)‖
            ≤ 1 * ‖κ (algebraMap _ K a)‖ := mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact ha }
  have hmem : ∀ r, r ∈ I ↔ ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1 := fun _ => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨by rw [Ne, Ideal.eq_top_iff_one, hmem]; simp, fun {a b} hab => ?_⟩
    rw [hmem, map_mul, map_mul, norm_mul] at hab
    rw [hmem, hmem]
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    have ha := le_antisymm (hle a) h.1
    have hb := le_antisymm (hle b) h.2
    rw [ha, hb, mul_one] at hab
    exact lt_irrefl _ hab
  have hpI : (p : NumberField.RingOfIntegers K) ∈ I := by
    rw [hmem, map_natCast, map_natCast,
      show (p : PadicComplex p) = ((p : Padic p) : PadicComplex p) from by simp,
      PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hpI
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact hp.out.ne_zero h2
  let la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := ⟨I, hIprime, hne⟩
  refine ⟨la, fun a => ?_⟩
  obtain ⟨n, d, h | h⟩ := la.exists_primeCompl_mul_eq_or_mul_eq a
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv : la.valuation K a = la.valuation K (algebraMap _ K n) := by
      rw [← h, map_mul, hvd, mul_one]
    have hN : ‖κ a‖ = ‖κ (algebraMap _ K n)‖ := by
      rw [← h, map_mul, norm_mul, hNd, mul_one]
    rw [hv, hN]
    exact iff_of_true (la.valuation_le_one (K := K) n) (hle n)
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv2 : la.valuation K a * la.valuation K (algebraMap _ K n) = 1 := by
      rw [← map_mul, h, hvd]
    have hN2 : ‖κ a‖ * ‖κ (algebraMap _ K n)‖ = 1 := by
      rw [← norm_mul, ← map_mul, h, hNd]
    have key1 : la.valuation K a ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha
        have h1 : 1 ≤ la.valuation K (algebraMap _ K n) := hv2 ▸ mul_le_of_le_one_left' ha
        exact (la.valuation_eq_one_iff_notMem (K := K)).mp
          (le_antisymm (la.valuation_le_one (K := K) n) h1)
      · intro hn
        have h1 := (la.valuation_eq_one_iff_notMem (K := K)).mpr hn
        rw [h1, mul_one] at hv2; exact hv2.le
    have key2 : ‖κ a‖ ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha hn
        have h1 : 1 ≤ ‖κ (algebraMap _ K n)‖ := by
          rw [← hN2]; exact mul_le_of_le_one_left (norm_nonneg _) ha
        exact absurd ((hmem n).mp hn) (not_lt.mpr h1)
      · intro hn
        have h1 : ‖κ (algebraMap _ K n)‖ = 1 := le_antisymm (hle n) (not_lt.mp hn)
        rw [h1, mul_one] at hN2; exact hN2.le
    rw [key1, key2]

private lemma valuation_perm_term {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

/-- Integral entries imply integral determinant under any valuation `v`. -/
theorem valuation_det_le_one_of_entries_le_one {K Γ ι : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (h1 : ∀ i j, v (M i j) ≤ 1) :
    v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

/-- An Iwahori-type matrix (integral entries, strictly sub-unit below the diagonal) has unit
determinant iff every diagonal entry is a unit (`CharpolyCoeffValuation.lean`). -/
theorem valuation_det_eq_one_iff_diag_eq_one {K Γ ι : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := fun σ j hj => by
    rw [valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have hex : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := hex
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

private lemma prod_lt_of_strictMono {Γ ι : Type*} [LinearOrderedCommGroupWithZero Γ] [LinearOrder ι]
    (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]; exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_sdiff S T, ← Finset.prod_inter_mul_prod_sdiff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

/-- Exact Newton-polygon valuation of characteristic polynomial coefficients for `diagonal d * M`
(`CharpolyCoeffValuation.lean`). -/
theorem charpoly_coeff_valuation {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) (hdet : v M.det = 1)
    (hmono : StrictMono fun i => v (d i)) (hd : ∀ i, d i ≠ 0) {k : ℕ} (hk : k ≤ n) :
    v ((Matrix.diagonal d * M).charpoly.coeff k) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  have hdiag := (valuation_det_eq_one_iff_diag_eq_one v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := fun S => by
    have hsub : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j; simp
    rw [hsub, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (valuation_det_eq_one_iff_diag_eq_one v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n))
      (fun i j => h1 _ _) (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (valuation_det_le_one_of_entries_le_one v _ fun i j => h1 _ _)) ?_
  refine prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 (v.ne_zero_iff.2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)

/-! ## 5. Homogeneous Polynomials, Covariant Degrees & Linear Substitution Bounds -/

/-- Homogeneous `MvPolynomial` evaluation scaling (`AevalMulHomog.lean`, `EvalSmulOfIsHomogeneous.lean`). -/
theorem aeval_mul_of_isHomogeneous {n : ℕ} {A G S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {P : MvPolynomial G A} (hP : P.IsHomogeneous n) (b : S) (x : G → S) :
    MvPolynomial.aeval (fun g : G => b * x g) P = b ^ n * MvPolynomial.aeval x P := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Degree bound over a distinguished variable subset `W` (`DegLESum.lean`). -/
def degLE {κ R : Type*} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) : Prop :=
  ∀ β : κ →₀ ℕ, MvPolynomial.coeff β F ≠ 0 → ∑ k ∈ W, β k ≤ n

theorem degLE_sum {κ R α : Type*} [CommRing R] {W : Finset κ} {n : ℕ} (s : Finset α)
    (F : α → MvPolynomial κ R) (h : ∀ a ∈ s, degLE W n (F a)) :
    degLE W n (∑ a ∈ s, F a) := by
  intro β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne

/-- Substituting polynomials of total degree `≤ 1` never increases `totalDegree`
(`TotalDegreeLinear.lean`). -/
theorem totalDegree_aeval_le_of_le_one {σ τ : Type*} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- Bi-linear matrix substitution on `MvPolynomial (ι × A ⊕ ι × B) ℂ` preserves `totalDegree` bounds
(`TotalDegreeLinear.lean`). -/
def linearSubst {ι A B : Type*} [Fintype ι] (g h : Matrix ι ι ℂ) :
    MvPolynomial (ι × A ⊕ ι × B) ℂ →ₐ[ℂ] MvPolynomial (ι × A ⊕ ι × B) ℂ :=
  MvPolynomial.aeval <|
    Sum.elim
      (fun x : ι × A => ∑ j : ι, MvPolynomial.C (g x.1 j) * MvPolynomial.X (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j : ι, MvPolynomial.C (h y.1 j) * MvPolynomial.X (Sum.inr (j, y.2)))

private lemma totalDegree_linear_le {ι τ : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → τ) :
    (∑ j : ι, (MvPolynomial.C (c j) : MvPolynomial τ ℂ) * MvPolynomial.X (v j)).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_X _).le

theorem totalDegree_linearSubst_le {ι A B : Type*} [Fintype ι] (g h : Matrix ι ι ℂ)
    (p : MvPolynomial (ι × A ⊕ ι × B) ℂ) :
    (linearSubst g h p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le_of_le_one _ ?_ p
  rintro (x | y)
  · exact totalDegree_linear_le (fun j => g x.1 j) (fun j => Sum.inl (j, x.2))
  · exact totalDegree_linear_le (fun j => h y.1 j) (fun j => Sum.inr (j, y.2))

/-- Injective ring-hom compatibility for weighted homogeneity and equivariant evaluation
(`WeightedHomogeneousMap.lean`). -/
theorem isWeightedHomogeneous_map_iff {R S σ M : Type*} [CommRing R] [CommRing S] [AddCommMonoid M]
    (φ : R →+* S) (hφ : Function.Injective φ) (w : σ → M) (ν : M) (f : MvPolynomial σ R) :
    MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔
      MvPolynomial.IsWeightedHomogeneous w f ν := by
  unfold MvPolynomial.IsWeightedHomogeneous
  refine forall_congr' fun d => ?_
  rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]

theorem aeval_map_eq_rename_map_iff {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (f : MvPolynomial σ R)
    (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ)
    (hg : ∀ v, MvPolynomial.map φ (gR v) = gS v) :
    MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔
      MvPolynomial.aeval gR f = MvPolynomial.rename ρ f := by
  have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
  subst hgS
  rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
    ← MvPolynomial.map_rename]
  exact (MvPolynomial.map_injective φ hφ).eq_iff

/-! ## 6. Product-Group Fixed Vectors (`FixPiIff.lean`, 8,029 L → 25 L) &
    Krull-Topology Decomposition Continuity (`CovariantDegrees.lean`, 5,600+ L → 20 L) -/

/-- The `H`-fixed submodule of a representation `ρ : Representation A G M`. -/
def fixedSubmodule {A G M : Type*} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (H : Subgroup G) : Submodule A M where
  carrier := {m | ∀ g ∈ H, ρ g m = m}
  add_mem' := fun {x y} hx hy g hg => by rw [map_add, hx g hg, hy g hg]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := fun a {x} hx g hg => by rw [map_smul, hx g hg]

/-- A vector is fixed by a finite product subgroup `Subgroup.pi Set.univ K` iff it is fixed by
each coordinate embedding `Pi.mulSingle j k` (`FixPiIff.lean`: 8,029 lines collapsed to 15!). -/
theorem fix_pi_iff {ι : Type*} [Finite ι] [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (∀ i, G i) M) (K : ∀ i, Subgroup (G i)) (m : M) :
    (∀ k ∈ Subgroup.pi Set.univ K, ρ k m = m) ↔
      ∀ j, ∀ k ∈ K j, ρ (Pi.mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i _ => ?_, fun h k hk => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hk
    · simp [Pi.mulSingle_eq_of_ne hij]
  · let H : Subgroup (∀ i, G i) :=
      { carrier := {g | ρ g m = m}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : ρ a m = m) (hb : ρ b m = m) =>
          show ρ (a * b) m = m by simp [ha, hb]
        inv_mem' := fun {a} (ha : ρ a m = m) =>
          show ρ a⁻¹ m = m by conv_lhs => rw [← ha, Representation.inv_self_apply] }
    exact Subgroup.pi_mem_of_mulSingle_mem (H := H) k fun i => h i _ (hk i trivial)

/-- Submodule-membership form of `fix_pi_iff` (replaces `mem_UC` in the 8,029-line `FixPiIff.lean`). -/
theorem mem_fixedSubmodule_pi_iff {ι : Type*} [Finite ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, Group (G i)] {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (∀ i, G i) M) (K : ∀ i, Subgroup (G i)) (m : M) :
    m ∈ fixedSubmodule ρ (Subgroup.pi Set.univ K) ↔
      ∀ j, m ∈ fixedSubmodule (ρ.comp (MonoidHom.mulSingle G j)) (K j) :=
  fix_pi_iff ρ K m

/-- Krull-topology continuity of restriction homomorphisms induced by a field embedding
`j : Ω →+* L` (collapses `CovariantDegrees.lean`'s 5,600+ lines of raw elaborated casts into
20 lines!). -/
theorem continuous_krull_restriction {E Ω F L : Type*} [Field E] [Field Ω] [Algebra E Ω]
    [Field F] [Field L] [Algebra F L] [Algebra.IsIntegral F L]
    (j : Ω →+* L) (H : Subgroup (L ≃ₐ[F] L))
    (rHom : H →* (Ω ≃ₐ[E] Ω))
    (hj_comm : ∀ (σ : H) (x : Ω), j (rHom σ x) = σ.1 (j x)) :
    Continuous rHom := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
  let _ : FiniteDimensional E M := hM
  let b := Module.finBasis E M
  have hU : ∀ᶠ σ : H in nhds 1, ∀ i, σ.1 (j (b i)) = j (b i) := by
    refine Filter.eventually_all.2 fun i => ?_
    have ho := (stabilizer_isOpen_of_isIntegral (K := F) (j (b i))).preimage
      (continuous_subtype_val (p := fun σ : L ≃ₐ[F] L => σ ∈ H))
    exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
  refine hU.mono fun σ hσ => hMs ?_
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have key : (rHom σ).toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap :=
    b.ext fun i => j.injective ((hj_comm σ (b i)).trans (hσ i))
  exact LinearMap.congr_fun key ⟨x, hx⟩

end RHDirect.CapelliCore

end
