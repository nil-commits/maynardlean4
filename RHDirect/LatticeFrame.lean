import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RHDirect.Interfaces

/-!
# RHDirect.LatticeFrame

Compact, direct, 0-`sorry`, 0-`axiom` formalization of the **Common Dual Lattice,
Gram-Matrix & Schur-Complement / Loewner Frame Density Bound** used in Pillar 2
(`TopDensityNGeSixteen`, `LinkMin`, `TraceSquareAndDiagBounds`, `CorankShare`,
`TheoremFSharp`).

## Structure

1. **Matrix Hilbert–Schmidt Geometry & Gram–Frame Trace Identities**:
   - Frobenius norm squared `hsSq`, exact identities for the ambient frame operator
     `frameOp B ga = ∑ u, ga u • (B u * (B u)ᴴ)` and Gram blocks
     `gramCross B ga u u' = √(ga u * ga u') • (B u)ᴴ * B u'`.
   - Cauchy–Schwarz trace lower bound and the uncompressed Gram-to-Frame theorem
     `gram_to_frame_bounds` (`GramInput` ⇒ `FrameTraceRatio (5 * sg)` ∧ `FrameDiagDefect e0`).

2. **Isometric Subspace Compression & Schur / Loewner Domination**:
   - Pythagorean Hilbert–Schmidt contraction `hsSq (Vᴴ * M * W) ≤ hsSq M`.
   - Loewner positive-semidefinite domination `0 ⪯ frameOp (B * V) ⪯ frameOp B`.
   - Compressed trace lower bound (`compress_trace_lower_bound`), diagonal defect
     (`compress_diag_defect_bound`), and trace-square ratio
     (`compress_trace_square_bound`: `5 * sg + 3 * √de`), plus word-count rank
     lower bound (`totalRank_ge_of_word_count`).

3. **Inner-Product Space Bessel-Frame-to-Corank Density Bound**:
   - Exact bridge between matrix Gram/frame quantities and `EuclideanSpace ℂ` linear maps.
   - Sharp Hilbert-space frame-to-corank density theorem (`frame_corank_density_bound`):
     `finrank (⨆ i, (Nτ i).map (B i))ᗮ ≤ (η + 4 * ε + 4 * √e) * finrank H`.
   - Ambient dual-lattice projection corank bound (`projected_ambient_corank_bound`) and
     end-to-end Gram-to-ambient-corank theorem (`projected_gram_corank_density_bound`).

4. **Corank-Share, Layer-Cake Integration & `RHDirect.BostSlopeFiber.SlopeIneq`**:
   - Corank-share tail bound (`corank_share_bound`), layer-cake integral inequality
     (`layer_cake_bound`), exact evaluation of `∫ τ in 0..HH, (4 * u / (u + τ) + c)`.
   - Direct deduction of `RHDirect.BostSlopeFiber.SlopeIneq` from corank density
     (`bost_slope_ineq_of_corank_density`) and directly from `GramInput` + isometric
     compression (`bost_slope_ineq_of_gram_input`), plus window-collapse monotonicity
     (`phi_mono`, `bost_slope_window_collapse`).
-/

open Finset Matrix Module LinearMap MeasureTheory Real
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHDirect.LatticeFrame

/-! ## Section 1: Matrix Hilbert–Schmidt Geometry & Gram–Frame Trace Identities -/

/-- Squared Hilbert–Schmidt (Frobenius) norm of a complex matrix. -/
def hsSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Hilbert–Schmidt (Frobenius) norm of a complex matrix. -/
def hsNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (hsSq M)

lemma hsSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma hsNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : 0 ≤ hsNorm M :=
  Real.sqrt_nonneg _

lemma hsNorm_sq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    hsNorm M ^ 2 = hsSq M :=
  Real.sq_sqrt (hsSq_nonneg M)

private lemma mul_conj_eq_norm_sq (z : ℂ) : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma trace_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = ((hsSq M : ℝ) : ℂ) := by
  unfold Matrix.trace hsSq
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact mul_conj_eq_norm_sq (M i j)

lemma hsSq_eq_re {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    hsSq M = (Mᴴ * M).trace.re := by
  rw [trace_conjTranspose_mul_self, Complex.ofReal_re]

lemma hsSq_conjTranspose {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    hsSq Mᴴ = hsSq M := by
  unfold hsSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.conjTranspose_apply]

lemma hsSq_smul {m n : Type*} [Fintype m] [Fintype n] (c : ℂ) (M : Matrix m n ℂ) :
    hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  unfold hsSq
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]

lemma hsSq_one (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold hsSq
  have h : ∀ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp [h]

lemma hsSq_reindex {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) :
    hsSq (Matrix.reindex e f M) = hsSq M := by
  unfold hsSq
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.symm.sum_comp]
  rfl

private lemma le_sqrt_of_sq_le' {a b : ℝ} (h : a ^ 2 ≤ b) : a ≤ Real.sqrt b := by
  rcases le_total a 0 with ha | ha
  · exact le_trans ha (Real.sqrt_nonneg b)
  · rw [← Real.sqrt_sq ha]
    exact Real.sqrt_le_sqrt h

lemma sum_sqrt_mul_sqrt_le {κ : Type*} [Fintype κ] (a b : κ → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) :
    ∑ u, Real.sqrt (a u) * Real.sqrt (b u) ≤ Real.sqrt (∑ u, a u) * Real.sqrt (∑ u, b u) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun u => Real.sqrt (a u)) (fun u => Real.sqrt (b u))
  have ea : ∀ u, Real.sqrt (a u) ^ 2 = a u := fun u => Real.sq_sqrt (ha u)
  have eb : ∀ u, Real.sqrt (b u) ^ 2 = b u := fun u => Real.sq_sqrt (hb u)
  simp only [ea, eb] at h
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun u _ => ha u)]
  exact le_sqrt_of_sq_le' h

/-- Cauchy–Schwarz inequality for the matrix trace pairing `|(X * Y).trace| ≤ ‖X‖_HS ‖Y‖_HS`. -/
lemma norm_trace_mul_le {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : m × n, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    calc ‖∑ i, ∑ j, X i j * Y j i‖
        ≤ ∑ i, ‖∑ j, X i j * Y j i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖X i j * Y j i‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = ∑ i, ∑ j, ‖X i j‖ * ‖Y j i‖ := by simp only [norm_mul]
      _ = ∑ p : m × n, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ :=
          (Fintype.sum_prod_type (fun p : m × n => ‖X p.1 p.2‖ * ‖Y p.2 p.1‖)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
  have hX : ∑ p : m × n, ‖X p.1 p.2‖ ^ 2 = hsSq X := Fintype.sum_prod_type _
  have hY : ∑ p : m × n, ‖Y p.2 p.1‖ ^ 2 = hsSq Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [hX, hY] at hcs
  have h2 : ∑ p : m × n, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ ≤ Real.sqrt (hsSq X * hsSq Y) :=
    le_sqrt_of_sq_le' hcs
  rw [Real.sqrt_mul (hsSq_nonneg X)] at h2
  exact le_trans h1 h2

lemma hsSq_add_le {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by
  have h1 : hsSq (A + B) ≤ ∑ p : m × n, (‖A p.1 p.2‖ + ‖B p.1 p.2‖) ^ 2 := by
    unfold hsSq
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A i j) (B i j)) 2
  have hexp : ∑ p : m × n, (‖A p.1 p.2‖ + ‖B p.1 p.2‖) ^ 2 =
      hsSq A + 2 * (∑ p : m × n, ‖A p.1 p.2‖ * ‖B p.1 p.2‖) + hsSq B := by
    have hA : ∑ p : m × n, ‖A p.1 p.2‖ ^ 2 = hsSq A := Fintype.sum_prod_type _
    have hB : ∑ p : m × n, ‖B p.1 p.2‖ ^ 2 = hsSq B := Fintype.sum_prod_type _
    have hpt : ∀ p : m × n, (‖A p.1 p.2‖ + ‖B p.1 p.2‖) ^ 2 =
        ‖A p.1 p.2‖ ^ 2 + 2 * (‖A p.1 p.2‖ * ‖B p.1 p.2‖) + ‖B p.1 p.2‖ ^ 2 := fun _ => by ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  have hA : ∑ p : m × n, ‖A p.1 p.2‖ ^ 2 = hsSq A := Fintype.sum_prod_type _
  have hB : ∑ p : m × n, ‖B p.1 p.2‖ ^ 2 = hsSq B := Fintype.sum_prod_type _
  rw [hA, hB] at hcs
  have hcr : ∑ p : m × n, ‖A p.1 p.2‖ * ‖B p.1 p.2‖ ≤ hsNorm A * hsNorm B := by
    have h := le_sqrt_of_sq_le' hcs
    rwa [Real.sqrt_mul (hsSq_nonneg A)] at h
  have hsq : (hsNorm A + hsNorm B) ^ 2 = hsSq A + 2 * (hsNorm A * hsNorm B) + hsSq B := by
    rw [add_sq, hsNorm_sq, hsNorm_sq]; ring
  linarith

lemma hsNorm_le_of_sq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    {e x : ℝ} (he : 0 ≤ e) (h : hsSq M ≤ e * x) :
    hsNorm M ≤ Real.sqrt e * Real.sqrt x := by
  unfold hsNorm
  rw [← Real.sqrt_mul he]
  exact Real.sqrt_le_sqrt h

/-- Cauchy–Schwarz trace lower bound: `n - √n * ‖K - I‖_HS ≤ Re(tr K)`. -/
theorem trace_re_lower_of_hsNorm (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    (n : ℝ) - Real.sqrt n * hsNorm (K - 1) ≤ K.trace.re := by
  have h1 : ‖(K - 1).trace‖ ≤ Real.sqrt n * hsNorm (K - 1) := by
    have h := norm_trace_mul_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
    rw [Matrix.one_mul] at h
    have hI : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
      unfold hsNorm; rw [hsSq_one]
    rwa [hI] at h
  have htr : (K - 1).trace.re = K.trace.re - (n : ℝ) := by
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_one, Fintype.card_fin]
    simp
  have habs : |(K - 1).trace.re| ≤ ‖(K - 1).trace‖ := Complex.abs_re_le_norm _
  have hneg : -‖(K - 1).trace‖ ≤ (K - 1).trace.re := (abs_le.mp habs).1
  linarith

lemma hsSq_le_of_sub_one (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by
  have h := hsSq_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) + (K - 1) = K := by abel
  have hI : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
    unfold hsNorm; rw [hsSq_one]
  rwa [h1, hI] at h

section FamilyGram

variable {ι : Type*} [Fintype ι] {D : ℕ} {d : ι → ℕ}

/-- Weighted cross-Gram block `√(γ_u γ_{u'}) · B_uᴴ B_{u'}` between subspaces `u` and `u'`. -/
def gramCross (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u u' : ι) :
    Matrix (Fin (d u)) (Fin (d u')) ℂ :=
  ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) • ((B u)ᴴ * B u')

/-- Weighted diagonal Gram block `γ_u · B_uᴴ B_u` on subspace `u`. -/
def gramDiag (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u : ι) :
    Matrix (Fin (d u)) (Fin (d u)) ℂ :=
  gramCross B ga u u

/-- Ambient frame operator `Q = ∑_u γ_u · B_u B_uᴴ` on `ℂ^D`. -/
def frameOp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ u, ((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)

/-- Total rank `R = ∑_u d_u`. -/
def totalRank (d : ι → ℕ) : ℝ := ∑ u, (d u : ℝ)

lemma totalRank_nonneg (d : ι → ℕ) : 0 ≤ totalRank d :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Frame trace-square ratio bound (`F1`): `Re(tr(Q²)) ≤ (1 + η) (Re(tr Q))² / D`. -/
def FrameTraceRatio (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (η : ℝ) : Prop :=
  (frameOp B ga * frameOp B ga).trace.re ≤ (1 + η) * (frameOp B ga).trace.re ^ 2 / (D : ℝ)

/-- Weighted diagonal Gram defect bound (`F2`): `∑_u ‖K_{u,u} - I‖_HS² ≤ e · R`. -/
def FrameDiagDefect (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (e : ℝ) : Prop :=
  ∑ u, hsSq (gramDiag B ga u - 1) ≤ e * totalRank d

/-- Off-diagonal Gram bound + diagonal near-isometry + ambient dimension ceiling (`InputS`). -/
def GramInput (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ u u', u ≠ u' → hsSq (gramCross B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar) ∧
  (∀ u, hsSq (gramDiag B ga u - 1) ≤ e0 * (d u : ℝ)) ∧
  (D : ℝ) ≤ (1 + η1) * Dstar

omit [Fintype ι] in
lemma gramDiag_eq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    gramDiag B ga u = ((ga u : ℝ) : ℂ) • ((B u)ᴴ * B u) := by
  unfold gramDiag gramCross
  rw [Real.sqrt_mul_self (hga u)]

lemma frameOp_trace (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) :
    (frameOp B ga).trace = ∑ u, (gramDiag B ga u).trace := by
  unfold frameOp
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [gramDiag_eq B ga hga u, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_comm]

omit [Fintype ι] in
lemma gramDiag_trace_eq_ofReal (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    (gramDiag B ga u).trace = ((ga u * hsSq (B u) : ℝ) : ℂ) := by
  rw [gramDiag_eq B ga hga u, Matrix.trace_smul, trace_conjTranspose_mul_self,
    smul_eq_mul, Complex.ofReal_mul]

lemma frameOp_trace_re (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) :
    (frameOp B ga).trace.re = ∑ u, (gramDiag B ga u).trace.re := by
  rw [frameOp_trace B ga hga, Complex.re_sum]

omit [Fintype ι] in
lemma hsSq_gramCross_eq_trace (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) (u u' : ι) :
    ((hsSq (gramCross B ga u u') : ℝ) : ℂ) =
      (((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ) * (((ga u' : ℝ) : ℂ) • (B u' * (B u')ᴴ))).trace := by
  rw [← trace_conjTranspose_mul_self]
  unfold gramCross
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  have hsq : ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) * ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) =
      ((ga u : ℝ) : ℂ) * ((ga u' : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_nonneg (hga u) (hga u')), Complex.ofReal_mul]
  have htr : ((B u')ᴴ * B u * ((B u)ᴴ * B u')).trace =
      (B u * (B u)ᴴ * (B u' * (B u')ᴴ)).trace := by
    calc ((B u')ᴴ * B u * ((B u)ᴴ * B u')).trace
        = ((B u')ᴴ * (B u * (B u)ᴴ * B u')).trace := by simp [Matrix.mul_assoc]
      _ = (B u * (B u)ᴴ * B u' * (B u')ᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (B u * (B u)ᴴ * (B u' * (B u')ᴴ)).trace := by simp [Matrix.mul_assoc]
  rw [htr]
  linear_combination hsq * (B u * (B u)ᴴ * (B u' * (B u')ᴴ)).trace

/-- Exact identity `Re(tr(Q²)) = ∑_{u, u'} ‖K_{u,u'}‖_HS²`. -/
theorem frameOp_sq_trace_re (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) :
    (frameOp B ga * frameOp B ga).trace.re = ∑ u, ∑ u', hsSq (gramCross B ga u u') := by
  have hc : (frameOp B ga * frameOp B ga).trace =
      ((∑ u, ∑ u', hsSq (gramCross B ga u u') : ℝ) : ℂ) := by
    unfold frameOp
    rw [Finset.sum_mul, Matrix.trace_sum]
    simp only [Finset.mul_sum, Matrix.trace_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
    exact (hsSq_gramCross_eq_trace B ga hga u u').symm
  rw [hc, Complex.ofReal_re]

lemma frameOp_trace_lower (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) {e0 : ℝ} (he : 0 ≤ e0)
    (hK : ∀ u, hsSq (gramDiag B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (1 - Real.sqrt e0) * totalRank d ≤ (frameOp B ga).trace.re := by
  rw [frameOp_trace_re B ga hga]
  unfold totalRank
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  have hlow := trace_re_lower_of_hsNorm (d u) (gramDiag B ga u)
  have hN := hsNorm_le_of_sq (gramDiag B ga u - 1) he (hK u)
  have hmul : Real.sqrt (d u) * hsNorm (gramDiag B ga u - 1) ≤ Real.sqrt e0 * (d u : ℝ) := by
    calc Real.sqrt (d u) * hsNorm (gramDiag B ga u - 1)
        ≤ Real.sqrt (d u) * (Real.sqrt e0 * Real.sqrt (d u)) :=
          mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg _)
      _ = Real.sqrt e0 * (Real.sqrt (d u) * Real.sqrt (d u)) := by ring
      _ = Real.sqrt e0 * (d u : ℝ) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  linarith

lemma frameOp_sq_trace_upper (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) {Dstar η0 η1 e0 : ℝ} (hD : 0 < Dstar) (hη0 : -1 ≤ η0) (he : 0 ≤ e0)
    (hS : GramInput B ga Dstar η0 η1 e0) :
    (frameOp B ga * frameOp B ga).trace.re ≤
      (1 + η0) * totalRank d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * totalRank d := by
  classical
  rw [frameOp_sq_trace_re B ga hga]
  have hpt : ∀ u u' : ι, hsSq (gramCross B ga u u') ≤
      (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar +
        (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) := by
    intro u u'
    by_cases h : u = u'
    · subst h
      simp only [↓reduceIte]
      have h1 : hsSq (gramCross B ga u u) ≤ (Real.sqrt (d u) + hsNorm (gramDiag B ga u - 1)) ^ 2 :=
        hsSq_le_of_sub_one (d u) (gramDiag B ga u)
      have hN := hsNorm_le_of_sq (gramDiag B ga u - 1) he (hS.2.1 u)
      have hsq : (Real.sqrt (d u) + hsNorm (gramDiag B ga u - 1)) ^ 2 ≤
          (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
        have h2 : Real.sqrt (d u) + hsNorm (gramDiag B ga u - 1) ≤
            (1 + Real.sqrt e0) * Real.sqrt (d u) := by linarith
        have h3 := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _)) h2 2
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h3
        exact h3
      have hnn : 0 ≤ (1 + η0) * (d u : ℝ) * (d u : ℝ) / Dstar :=
        div_nonneg (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hD.le
      linarith
    · simp only [h, ↓reduceIte, add_zero]
      exact hS.1 u u' h
  calc ∑ u, ∑ u', hsSq (gramCross B ga u u')
      ≤ ∑ u, ∑ u', ((1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar +
          (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hpt u u'
    _ = (∑ u, ∑ u', (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar) +
          (∑ u, ∑ u', if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = (1 + η0) * totalRank d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * totalRank d := by
        congr 1
        · unfold totalRank
          have h1 : ∀ u, ∑ u', (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar =
              ((1 + η0) / Dstar) * (d u : ℝ) * ∑ u', (d u' : ℝ) := fun u => by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u' _ => by ring
          simp only [h1, ← Finset.sum_mul, ← Finset.mul_sum]
          ring
        · unfold totalRank
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]

private lemma ratio_step_aux {T2 T1 R Dst D X L c b : ℝ}
    (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst) (hL : 0 ≤ L) (hR : 0 < R)
    (hb : 0 < b) (hT1 : b * R ≤ T1) (hT2 : T2 ≤ X * R ^ 2 / Dst) (hX : 0 ≤ X)
    (hnum : L * X ≤ c * b ^ 2) :
    T2 ≤ c * T1 ^ 2 / D := by
  have h1 : T2 * D ≤ (X * R ^ 2 / Dst) * (L * Dst) :=
    mul_le_mul hT2 hDD hD.le (div_nonneg (mul_nonneg hX (sq_nonneg R)) hDs.le)
  have h2 : (X * R ^ 2 / Dst) * (L * Dst) = L * X * R ^ 2 := by field_simp [hDs.ne']
  have h3 : (b * R) ^ 2 ≤ T1 ^ 2 := pow_le_pow_left₀ (mul_nonneg hb.le hR.le) hT1 2
  have h4 : L * X * R ^ 2 ≤ c * (b * R) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hnum (sq_nonneg R)
    linarith
  have hc0 : 0 ≤ c := by
    have hLX : 0 ≤ L * X := mul_nonneg hL hX
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    by_contra h
    push Not at h
    have : c * b ^ 2 < 0 := mul_neg_of_neg_of_pos h hb2
    linarith
  have h5 : c * (b * R) ^ 2 ≤ c * T1 ^ 2 := mul_le_mul_of_nonneg_left h3 hc0
  rw [le_div_iff₀ hD]
  linarith

private lemma num_uncompressed {s η0 η1 a : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1 : η1 ≤ s / 2) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * (1 + η0 + s * (1 + a) ^ 2) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by
  have h1 : 1 + η1 ≤ 1 + s / 2 := by linarith
  have h2 : 1 + η0 + s * (1 + a) ^ 2 ≤ 1 + s / 2 + s * (1 + s / 2) ^ 2 := by
    have : (1 + a) ^ 2 ≤ (1 + s / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  have h3 : 0 ≤ 1 + η0 + s * (1 + a) ^ 2 := by nlinarith [sq_nonneg (1 + a)]
  have h4 : (1 + η1) * (1 + η0 + s * (1 + a) ^ 2) ≤
      (1 + s / 2) * (1 + s / 2 + s * (1 + s / 2) ^ 2) := by
    rcases le_total 0 (1 + η1) with h1p | h1n
    · exact mul_le_mul h1 h2 h3 (by linarith)
    · have hlhs : (1 + η1) * (1 + η0 + s * (1 + a) ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1n h3
      have hrhs : 0 ≤ (1 + s / 2) * (1 + s / 2 + s * (1 + s / 2) ^ 2) := by positivity
      linarith
  have h5 : (1 - s / 2) ^ 2 ≤ (1 - a) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hpoly : (1 + s / 2) * (1 + s / 2 + s * (1 + s / 2) ^ 2) ≤ (1 + 5 * s) * (1 - s / 2) ^ 2 := by
    have hdiff : (1 + 5 * s) * (1 - s / 2) ^ 2 - (1 + s / 2) * (1 + s / 2 + s * (1 + s / 2) ^ 2) =
        s * (2 - 13 / 2 * s + 1 / 2 * s ^ 2 - 1 / 8 * s ^ 3) := by ring
    have hs2 : s ^ 2 ≤ 1 / 16 := by nlinarith
    have hs3 : s ^ 3 ≤ 1 / 64 := by nlinarith
    have hpos : 0 ≤ 2 - 13 / 2 * s + 1 / 2 * s ^ 2 - 1 / 8 * s ^ 3 := by nlinarith
    nlinarith
  nlinarith

/-- **Uncompressed Gram-to-Frame Theorem** (`TraceSquareAndDiagBounds`):
Controlled off-diagonal and diagonal Gram blocks with `Dstar / sg ≤ totalRank d` yield
both the frame trace-square ratio bound `FrameTraceRatio B ga (5 * sg)` and the
diagonal defect bound `FrameDiagDefect B ga e0`. -/
theorem gram_to_frame_bounds (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (Dstar sg η0 η1 e0 : ℝ) (hga : ∀ u, 0 ≤ ga u) (hDs : 0 < Dstar) (hsg : 0 < sg)
    (hsg4 : sg ≤ 1 / 4) (hR : Dstar / sg ≤ totalRank d)
    (hη0 : -1 ≤ η0) (hη0' : η0 ≤ sg / 2) (hη1 : η1 ≤ sg / 2)
    (he0 : 0 ≤ e0) (hse : Real.sqrt e0 ≤ sg / 2)
    (hS : GramInput B ga Dstar η0 η1 e0) :
    FrameTraceRatio B ga (5 * sg) ∧ FrameDiagDefect B ga e0 ∧ e0 ≤ 1 / 4 := by
  have he4 : e0 ≤ 1 / 4 := by
    have hsq : Real.sqrt e0 ^ 2 ≤ (sg / 2) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hse 2
    rw [Real.sq_sqrt he0] at hsq
    nlinarith
  have hF2 : FrameDiagDefect B ga e0 := by
    unfold FrameDiagDefect totalRank
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => hS.2.1 u
  refine ⟨?_, hF2, he4⟩
  unfold FrameTraceRatio
  by_cases hD0 : D = 0
  · subst hD0
    simp only [Nat.cast_zero, div_zero]
    have h0 : frameOp B ga = 0 := Matrix.ext fun i _ => Fin.elim0 i
    simp [h0]
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD0)
  have hRpos : 0 < totalRank d := lt_of_lt_of_le (div_pos hDs hsg) hR
  have hT1 := frameOp_trace_lower B ga hga he0 hS.2.1
  have hT2_0 := frameOp_sq_trace_upper B ga hga hDs hη0 he0 hS
  have hRterm : totalRank d ≤ sg * totalRank d ^ 2 / Dstar := by
    have h1 : Dstar ≤ totalRank d * sg := (div_le_iff₀ hsg).mp hR
    have h2 : Dstar * totalRank d ≤ sg * totalRank d ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 hRpos.le; linarith
    exact (le_div_iff₀ hDs).mpr (by linarith)
  have hT2 : (frameOp B ga * frameOp B ga).trace.re ≤
      (1 + η0 + sg * (1 + Real.sqrt e0) ^ 2) * totalRank d ^ 2 / Dstar := by
    have hmul := mul_le_mul_of_nonneg_left hRterm (sq_nonneg (1 + Real.sqrt e0))
    have heq : (1 + η0) * totalRank d ^ 2 / Dstar +
        (1 + Real.sqrt e0) ^ 2 * (sg * totalRank d ^ 2 / Dstar) =
        (1 + η0 + sg * (1 + Real.sqrt e0) ^ 2) * totalRank d ^ 2 / Dstar := by ring
    linarith
  have hLpos : 0 ≤ 1 + η1 := by
    have : (0 : ℝ) < (1 + η1) * Dstar := lt_of_lt_of_le hDpos hS.2.2
    exact le_of_lt (pos_of_mul_pos_left this hDs.le)
  have hXnn : 0 ≤ 1 + η0 + sg * (1 + Real.sqrt e0) ^ 2 := by
    nlinarith [sq_nonneg (1 + Real.sqrt e0)]
  exact ratio_step_aux hDpos hDs hS.2.2 hLpos hRpos (by linarith) hT1 hT2 hXnn
    (num_uncompressed hsg hsg4 hη0 hη0' hη1 (Real.sqrt_nonneg _) hse)

end FamilyGram

/-! ## Section 2: Isometric Subspace Compression & Schur / Loewner Domination -/

section IsometricCompression

lemma proj_conjTranspose {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (V : Matrix m k ℂ) : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul]

lemma proj_idempotent {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have h1 : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    calc V * Vᴴ * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * (1 : Matrix k k ℂ) * Vᴴ := by rw [hV]
      _ = V * Vᴴ := by simp
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h1]
  abel

/-- Pythagorean Hilbert–Schmidt decomposition under an isometry `V` (`Vᴴ * V = 1`). -/
theorem hsSq_isom_split {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
    [DecidableEq m] [DecidableEq k] (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by
  have hP : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [proj_conjTranspose V, proj_idempotent V hV]
  have h1 : ((Vᴴ * M)ᴴ * (Vᴴ * M)).trace = (Mᴴ * (V * Vᴴ) * M).trace := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h2 : (((1 - V * Vᴴ) * M)ᴴ * ((1 - V * Vᴴ) * M)).trace =
      (Mᴴ * (1 - V * Vᴴ) * M).trace := by
    have : ((1 - V * Vᴴ) * M)ᴴ * ((1 - V * Vᴴ) * M) =
        Mᴴ * ((1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ)) * M := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hP]
  have hsum : Mᴴ * (V * Vᴴ) * M + Mᴴ * (1 - V * Vᴴ) * M = Mᴴ * M := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  have htr : ((Vᴴ * M)ᴴ * (Vᴴ * M)).trace + (((1 - V * Vᴴ) * M)ᴴ * ((1 - V * Vᴴ) * M)).trace =
      (Mᴴ * M).trace := by
    rw [h1, h2, ← Matrix.trace_add, hsum]
  rw [trace_conjTranspose_mul_self, trace_conjTranspose_mul_self,
    trace_conjTranspose_mul_self, ← Complex.ofReal_add] at htr
  exact (Complex.ofReal_injective htr).symm

lemma hsSq_isom_left_le {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
    [DecidableEq m] [DecidableEq k] (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq (Vᴴ * M) ≤ hsSq M := by
  have h := hsSq_isom_split V hV M
  have hnn := hsSq_nonneg ((1 - V * Vᴴ) * M)
  linarith

/-- Two-sided isometric compression contracts the Hilbert–Schmidt norm:
`‖Vᴴ M W‖_HS² ≤ ‖M‖_HS²`. -/
theorem hsSq_isom_compress {a b c e : ℕ}
    (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1)
    (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by
  calc hsSq (Vᴴ * M * W)
      = hsSq (Wᴴ * (Vᴴ * M)ᴴ) := by
        rw [← hsSq_conjTranspose, Matrix.conjTranspose_mul]
    _ ≤ hsSq (Vᴴ * M)ᴴ := hsSq_isom_left_le W hW (Vᴴ * M)ᴴ
    _ = hsSq (Vᴴ * M) := hsSq_conjTranspose _
    _ ≤ hsSq M := hsSq_isom_left_le V hV M

lemma trace_proj_compl (n k : ℕ) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).trace = (((n : ℝ) - k : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_mul_comm, hV, Matrix.trace_one,
    Fintype.card_fin, Fintype.card_fin]
  simp

/-- Isometric trace-compression gap on a single near-identity Gram block. -/
lemma single_block_compression_gap (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0)
    (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧
    K.trace.re - (Vᴴ * K * V).trace.re
      ≤ ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by
  have hP : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [proj_conjTranspose V, proj_idempotent V hV]
  have hnk : hsSq (1 - V * Vᴴ) = (n : ℝ) - k := by
    have h := trace_conjTranspose_mul_self (1 - V * Vᴴ)
    rw [hP, trace_proj_compl n k V hV] at h
    exact (Complex.ofReal_injective h).symm
  have hnk0 : 0 ≤ (n : ℝ) - k := by rw [← hnk]; exact hsSq_nonneg _
  refine ⟨hnk0, ?_⟩
  have hcyc : (Vᴴ * K * V).trace = (K * (V * Vᴴ)).trace := by
    rw [Matrix.trace_mul_comm (Vᴴ * K) V, Matrix.trace_mul_comm K (V * Vᴴ), Matrix.mul_assoc]
  have htr : K.trace - (Vᴴ * K * V).trace =
      (1 - V * Vᴴ).trace + ((K - 1) * (1 - V * Vᴴ)).trace := by
    rw [hcyc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
    ring
  have hcs := norm_trace_mul_le (K - 1) (1 - V * Vᴴ)
  have hN1 : hsNorm (1 - V * Vᴴ) = Real.sqrt ((n : ℝ) - k) := by unfold hsNorm; rw [hnk]
  rw [hN1] at hcs
  have hNK := hsNorm_le_of_sq (K - 1) he hK
  have hre : (K.trace - (Vᴴ * K * V).trace).re =
      ((n : ℝ) - k) + ((K - 1) * (1 - V * Vᴴ)).trace.re := by
    rw [htr, Complex.add_re, trace_proj_compl n k V hV, Complex.ofReal_re]
  rw [Complex.sub_re] at hre
  have habs : ((K - 1) * (1 - V * Vᴴ)).trace.re ≤ ‖((K - 1) * (1 - V * Vᴴ)).trace‖ :=
    (abs_le.mp (Complex.abs_re_le_norm _)).2
  have hm := mul_le_mul_of_nonneg_left hNK (Real.sqrt_nonneg ((n : ℝ) - k))
  linarith

variable {ι : Type*} [Fintype ι] {D : ℕ} {d r : ι → ℕ}

/-- A family of isometric subspace inclusions `V_u : ℂ^{r_u} → ℂ^{d_u}` (`V_uᴴ V_u = I`). -/
def IsIsometryFamily (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : Prop :=
  ∀ u, (V u)ᴴ * V u = 1

/-- Compressed frame family `(B * V)_u := B_u V_u`. -/
def compressFamily (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ :=
  fun u => B u * V u

omit [Fintype ι] in
lemma gramCross_compress (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (u u' : ι) :
    gramCross (compressFamily B V) ga u u' = (V u)ᴴ * gramCross B ga u u' * V u' := by
  unfold gramCross compressFamily
  simp only [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

omit [Fintype ι] in
lemma gramDiag_compress_sub_one (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ)
    (hV : IsIsometryFamily V) (u : ι) :
    gramDiag (compressFamily B V) ga u - 1 = (V u)ᴴ * (gramDiag B ga u - 1) * V u := by
  unfold gramDiag
  rw [gramCross_compress]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV u]

private lemma posSemidef_sum {α : Type*} [Fintype α] {s : Finset α}
    {f : α → Matrix (Fin D) (Fin D) ℂ} (hf : ∀ a ∈ s, (f a).PosSemidef) :
    (∑ a ∈ s, f a).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.PosSemidef.zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- **Loewner Positivity**: The ambient frame operator `frameOp B ga` is positive semidefinite
for nonnegative weights `ga`. -/
theorem frameOp_posSemidef (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ)
    (hga : ∀ u, 0 ≤ ga u) :
    (frameOp B ga).PosSemidef := by
  unfold frameOp
  refine posSemidef_sum fun u _ => ?_
  have h1 : (B u * (B u)ᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose (B u)
  have hsmul : ((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ) = (ga u) • (B u * (B u)ᴴ) := by
    ext i j; simp [Complex.real_smul]
  rw [hsmul]
  exact h1.smul (hga u)

/-- **Schur / Loewner Domination under Isometric Compression**:
`0 ⪯ frameOp (B * V) ga ⪯ frameOp B ga`. -/
theorem frameOp_compress_loewner (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ)
    (hV : IsIsometryFamily V) (hga : ∀ u, 0 ≤ ga u) :
    (frameOp (compressFamily B V) ga).PosSemidef ∧
    (frameOp B ga - frameOp (compressFamily B V) ga).PosSemidef := by
  refine ⟨frameOp_posSemidef (compressFamily B V) ga hga, ?_⟩
  have hsub : frameOp B ga - frameOp (compressFamily B V) ga =
      ∑ u, ((ga u : ℝ) : ℂ) • ((B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ) := by
    unfold frameOp compressFamily
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hP : (1 - V u * (V u)ᴴ) * (1 - V u * (V u)ᴴ)ᴴ = 1 - V u * (V u)ᴴ := by
      rw [proj_conjTranspose (V u), proj_idempotent (V u) (hV u)]
    have hmul : (B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ =
        B u * (B u)ᴴ - (B u * V u) * (B u * V u)ᴴ := by
      calc (B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ
          = B u * ((1 - V u * (V u)ᴴ) * (1 - V u * (V u)ᴴ)ᴴ) * (B u)ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = B u * (1 - V u * (V u)ᴴ) * (B u)ᴴ := by rw [hP]
        _ = B u * (B u)ᴴ - (B u * V u) * (B u * V u)ᴴ := by
            simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hmul, smul_sub]
  rw [hsub]
  refine posSemidef_sum fun u _ => ?_
  have h1 : ((B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose _
  have hsmul : ((ga u : ℝ) : ℂ) • ((B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ) =
      (ga u) • ((B u * (1 - V u * (V u)ᴴ)) * (B u * (1 - V u * (V u)ᴴ))ᴴ) := by
    ext i j; simp [Complex.real_smul]
  rw [hsmul]
  exact h1.smul (hga u)

/-- **Compressed Trace Lower Bound** (`RamTrace`):
Isometric compression with total codimension fraction `≤ de` lowers `Re(tr Q)` by at most
`(de + √(de * e0)) * totalRank d`. -/
theorem compress_trace_lower_bound (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ)
    (hV : IsIsometryFamily V) (hga : ∀ u, 0 ≤ ga u) (hde : 0 ≤ de) (he : 0 ≤ e0)
    (hK : ∀ u, hsSq (gramDiag B ga u - 1) ≤ e0 * (d u : ℝ))
    (hcor : ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * totalRank d) :
    (frameOp B ga).trace.re - (de + Real.sqrt (de * e0)) * totalRank d ≤
      (frameOp (compressFamily B V) ga).trace.re := by
  have hgap := fun u => single_block_compression_gap (d u) (r u) (gramDiag B ga u) (V u) (hV u)
    he (hK u)
  have hnn : ∀ u, 0 ≤ (d u : ℝ) - (r u : ℝ) := fun u => (hgap u).1
  have hCS := sum_sqrt_mul_sqrt_le (fun u => (d u : ℝ) - (r u : ℝ)) (fun u => (d u : ℝ))
    hnn (fun u => Nat.cast_nonneg _)
  have h3 : Real.sqrt (∑ u, ((d u : ℝ) - (r u : ℝ))) ≤
      Real.sqrt de * Real.sqrt (totalRank d) := by
    rw [← Real.sqrt_mul hde]
    exact Real.sqrt_le_sqrt hcor
  have hT : Real.sqrt (totalRank d) * Real.sqrt (totalRank d) = totalRank d :=
    Real.mul_self_sqrt (totalRank_nonneg d)
  have h4 : ∑ u, Real.sqrt ((d u : ℝ) - (r u : ℝ)) * Real.sqrt (d u) ≤
      Real.sqrt de * totalRank d := by
    have hm := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (totalRank d))
    rw [mul_assoc, hT] at hm
    exact le_trans hCS hm
  have h5 : ∑ u, Real.sqrt ((d u : ℝ) - (r u : ℝ)) * (Real.sqrt e0 * Real.sqrt (d u)) ≤
      Real.sqrt (de * e0) * totalRank d := by
    have hre : ∑ u, Real.sqrt ((d u : ℝ) - (r u : ℝ)) * (Real.sqrt e0 * Real.sqrt (d u)) =
        Real.sqrt e0 * ∑ u, Real.sqrt ((d u : ℝ) - (r u : ℝ)) * Real.sqrt (d u) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [hre, Real.sqrt_mul hde]
    have hm := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg e0)
    linarith
  have hsum_gap : (frameOp B ga).trace.re - (frameOp (compressFamily B V) ga).trace.re ≤
      (∑ u, ((d u : ℝ) - (r u : ℝ))) +
        ∑ u, Real.sqrt ((d u : ℝ) - (r u : ℝ)) * (Real.sqrt e0 * Real.sqrt (d u)) := by
    rw [frameOp_trace_re B ga hga, frameOp_trace_re (compressFamily B V) ga hga,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : gramDiag (compressFamily B V) ga u = (V u)ᴴ * gramDiag B ga u * V u :=
      gramCross_compress B V ga u u
    rw [heq]
    exact (hgap u).2
  linarith

/-- **Compressed Diagonal Defect Bound** (`CompressDiagDefectBound`):
Under isometric compression with codimension share `de ≤ 1/2`, the remaining rank is at least
`(1 - de) * totalRank d` and the diagonal defect stays bounded by `2 * e0`. -/
theorem compress_diag_defect_bound (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ)
    (hV : IsIsometryFamily V) (hde2 : de ≤ 1 / 2) (he : 0 ≤ e0)
    (hK : ∀ u, hsSq (gramDiag B ga u - 1) ≤ e0 * (d u : ℝ))
    (hcor : ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * totalRank d) :
    (1 - de) * totalRank d ≤ totalRank r ∧ FrameDiagDefect (compressFamily B V) ga (2 * e0) := by
  have hRr : (1 - de) * totalRank d ≤ totalRank r := by
    unfold totalRank at hcor ⊢
    rw [Finset.sum_sub_distrib] at hcor
    linarith
  refine ⟨hRr, ?_⟩
  unfold FrameDiagDefect
  have h1 : ∑ u, hsSq (gramDiag (compressFamily B V) ga u - 1) ≤ e0 * totalRank d := by
    unfold totalRank
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [gramDiag_compress_sub_one B V ga hV u]
    exact le_trans (hsSq_isom_compress (V u) (hV u) (V u) (hV u) _) (hK u)
  have h2 : totalRank d ≤ 2 * totalRank r := by
    have hRnn := totalRank_nonneg d
    nlinarith
  nlinarith

private lemma num_compressed {s a t : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by
  have h_le : 1 - a - t ^ 2 - t * a ≥ (1 - a) * (1 - t ^ 2 / (1 - a) - t * a / (1 - a)) := by
    have h1a : 0 < 1 - a := by linarith
    have : (1 - a) * (1 - t ^ 2 / (1 - a) - t * a / (1 - a)) = 1 - a - t ^ 2 - t * a := by
      field_simp [h1a.ne']
    linarith
  have hr : 1 - a - t ^ 2 - t * a ≥ (1 - a) * (1 - t * (t + a) / (1 - a)) := by
    have h1a : 0 < 1 - a := by linarith
    have : (1 - a) * (1 - t * (t + a) / (1 - a)) = 1 - a - t ^ 2 - t * a := by
      field_simp [h1a.ne']; ring
    linarith
  have h1a : 39 / 40 ≤ 1 - a := by linarith
  have hta : t + a ≤ 21 / 40 := by linarith
  have hfac : t * (t + a) ≤ 11 / 20 * t * (1 - a) := by nlinarith
  have h1m : (1 - 11 / 20 * t) * (1 - a) ≤ 1 - a - t ^ 2 - t * a := by nlinarith
  have h1m_nn : 0 ≤ (1 - 11 / 20 * t) * (1 - a) := by nlinarith
  have hsq : ((1 - 11 / 20 * t) * (1 - a)) ^ 2 ≤ (1 - a - t ^ 2 - t * a) ^ 2 :=
    pow_le_pow_left₀ h1m_nn h1m 2
  have hpoly : 1 + 5 * s ≤ (1 + 5 * s + 3 * t) * (1 - 11 / 20 * t) ^ 2 := by
    have hexp : (1 + 5 * s + 3 * t) * (1 - 11 / 20 * t) ^ 2 - (1 + 5 * s) =
        t * (3 - (11 / 10) * (1 + 5 * s) - (33 / 10 - (121 / 400) * (1 + 5 * s)) * t +
          (363 / 400) * t ^ 2) := by ring
    have hbr : 0 ≤ 3 - (11 / 10) * (1 + 5 * s) - (33 / 10 - (121 / 400) * (1 + 5 * s)) * t +
        (363 / 400) * t ^ 2 := by
      nlinarith [sq_nonneg t]
    nlinarith
  have h1 : (1 + 5 * s) * (1 - a) ^ 2 ≤
      (1 + 5 * s + 3 * t) * ((1 - 11 / 20 * t) * (1 - a)) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hpoly (sq_nonneg (1 - a))
    linarith
  have h2 : (1 + 5 * s + 3 * t) * ((1 - 11 / 20 * t) * (1 - a)) ^ 2 ≤
      (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith

/-- **Compressed Frame Trace-Square Ratio Bound** (`CompressTraceSquareBound`):
Under isometric compression `B_u ↦ B_u V_u` with codimension share `de ≤ 1/4`,
the compressed frame operator satisfies
`FrameTraceRatio (compressFamily B V) ga (5 * sg + 3 * Real.sqrt de)`. -/
theorem compress_trace_square_bound (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ)
    (Dstar sg η0 η1 e0 de : ℝ)
    (hV : IsIsometryFamily V) (hga : ∀ u, 0 ≤ ga u) (hDs : 0 < Dstar) (hsg : 0 < sg)
    (hsg20 : sg ≤ 1 / 20) (hR : Dstar / sg ≤ totalRank d)
    (hη0 : -1 ≤ η0) (hη0' : η0 ≤ sg / 2) (hη1 : η1 ≤ sg / 2)
    (he0 : 0 ≤ e0) (hse : Real.sqrt e0 ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4)
    (hcor : ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * totalRank d)
    (hS : GramInput B ga Dstar η0 η1 e0) :
    FrameTraceRatio (compressFamily B V) ga (5 * sg + 3 * Real.sqrt de) := by
  unfold FrameTraceRatio
  by_cases hD0 : D = 0
  · subst hD0
    simp only [Nat.cast_zero, div_zero]
    have h0 : frameOp (compressFamily B V) ga = 0 := Matrix.ext fun i _ => Fin.elim0 i
    simp [h0]
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD0)
  have hRpos : 0 < totalRank d := lt_of_lt_of_le (div_pos hDs hsg) hR
  -- Upper bound on tr(Q_compressed^2) via HS contraction of every cross-Gram block
  have hQsq_le : (frameOp (compressFamily B V) ga * frameOp (compressFamily B V) ga).trace.re ≤
      (frameOp B ga * frameOp B ga).trace.re := by
    rw [frameOp_sq_trace_re (compressFamily B V) ga hga, frameOp_sq_trace_re B ga hga]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => ?_
    rw [gramCross_compress]
    exact hsSq_isom_compress (V u) (hV u) (V u') (hV u') _
  have hT2_0 := le_trans hQsq_le (frameOp_sq_trace_upper B ga hga hDs hη0 he0 hS)
  have hRterm : totalRank d ≤ sg * totalRank d ^ 2 / Dstar := by
    have h1 : Dstar ≤ totalRank d * sg := (div_le_iff₀ hsg).mp hR
    have h2 : Dstar * totalRank d ≤ sg * totalRank d ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 hRpos.le; linarith
    exact (le_div_iff₀ hDs).mpr (by linarith)
  have hT2 : (frameOp (compressFamily B V) ga * frameOp (compressFamily B V) ga).trace.re ≤
      (1 + η0 + sg * (1 + Real.sqrt e0) ^ 2) * totalRank d ^ 2 / Dstar := by
    have hmul := mul_le_mul_of_nonneg_left hRterm (sq_nonneg (1 + Real.sqrt e0))
    have heq : (1 + η0) * totalRank d ^ 2 / Dstar +
        (1 + Real.sqrt e0) ^ 2 * (sg * totalRank d ^ 2 / Dstar) =
        (1 + η0 + sg * (1 + Real.sqrt e0) ^ 2) * totalRank d ^ 2 / Dstar := by ring
    linarith
  -- Lower bound on tr(Q_compressed)
  have hT1_orig := frameOp_trace_lower B ga hga he0 hS.2.1
  have hT1_gap := compress_trace_lower_bound B V ga de e0 hV hga hde0 he0 hS.2.1 hcor
  set t := Real.sqrt de
  set a := Real.sqrt e0
  have ht0 : 0 ≤ t := Real.sqrt_nonneg de
  have ht2 : t ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hde4
  have htsq : t ^ 2 = de := Real.sq_sqrt hde0
  have hta : Real.sqrt (de * e0) = t * a := Real.sqrt_mul hde0 e0
  have hT1 : (1 - a - t ^ 2 - t * a) * totalRank d ≤
      (frameOp (compressFamily B V) ga).trace.re := by
    rw [htsq, ← hta]
    linarith
  have hb : 0 < 1 - a - t ^ 2 - t * a := by
    have ha0 : 0 ≤ a := Real.sqrt_nonneg e0
    nlinarith
  have hLpos : 0 ≤ 1 + η1 := by
    have : (0 : ℝ) < (1 + η1) * Dstar := lt_of_lt_of_le hDpos hS.2.2
    exact le_of_lt (pos_of_mul_pos_left this hDs.le)
  have hXnn : 0 ≤ 1 + η0 + sg * (1 + a) ^ 2 := by nlinarith [sq_nonneg (1 + a)]
  have hnum1 := num_uncompressed hsg (by linarith) hη0 hη0' hη1 (Real.sqrt_nonneg _) hse
  have hnum2 := num_compressed hsg hsg20 (Real.sqrt_nonneg _) hse ht0 ht2
  have hnum : (1 + η1) * (1 + η0 + sg * (1 + a) ^ 2) ≤
      (1 + (5 * sg + 3 * t)) * (1 - a - t ^ 2 - t * a) ^ 2 := by
    have := le_trans hnum1 hnum2
    linarith
  exact ratio_step_aux hDpos hDs hS.2.2 hLpos hRpos hb hT1 hT2 hXnn hnum

/-- **Word-Count Rank Lower Bound** (`word_count_bound_holds` in `TopDensityNGeSixteen.lean`):
If there are at least `C0 * Gam^2 / sg` words/characters each contributing rank at least
`Dstar / (C0 * Gam^2)`, then `Dstar / sg ≤ totalRank d`. -/
theorem totalRank_ge_of_word_count (d : ι → ℕ) (Dstar sg C0 Gam : ℝ)
    (hD : 0 < Dstar) (hsg : 0 < sg) (hC : 0 < C0) (hG : 0 < Gam)
    (hCard : C0 * Gam ^ 2 / sg ≤ (Fintype.card ι : ℝ))
    (hd : ∀ u : ι, Dstar * (Gam ^ 2)⁻¹ / C0 ≤ (d u : ℝ)) :
    Dstar / sg ≤ totalRank d := by
  have h1 : (Fintype.card ι : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) ≤ totalRank d := by
    unfold totalRank
    calc (Fintype.card ι : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0)
        = ∑ _u : ι, Dstar * (Gam ^ 2)⁻¹ / C0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ u : ι, (d u : ℝ) := Finset.sum_le_sum fun u _ => hd u
  have h2 : 0 ≤ Dstar * (Gam ^ 2)⁻¹ / C0 := by positivity
  have h3 : C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) = Dstar / sg := by
    field_simp [hsg.ne', hC.ne', hG.ne']
  calc Dstar / sg = C0 * Gam ^ 2 / sg * (Dstar * (Gam ^ 2)⁻¹ / C0) := h3.symm
    _ ≤ (Fintype.card ι : ℝ) * (Dstar * (Gam ^ 2)⁻¹ / C0) :=
        mul_le_mul_of_nonneg_right hCard h2
    _ ≤ totalRank d := h1

end IsometricCompression

/-! ## Section 3: Inner-Product Space Bessel-Frame-to-Corank Density Theorem -/

section InnerProductFrame

/-- Hilbert–Schmidt norm squared of a linear map between finite-dimensional complex
inner product spaces. -/
def opHsSq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) : ℝ :=
  (LinearMap.trace ℂ E (LinearMap.adjoint A ∘ₗ A)).re

/-- Weighted diagonal Gram operator `c · B* B` on `V`. -/
def opFrameK {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ℝ) (B : V →ₗ[ℂ] H) : V →ₗ[ℂ] V :=
  (c : ℂ) • (LinearMap.adjoint B ∘ₗ B)

/-- Ambient frame operator `∑_i c_i · B_i B_i*` on `H`. -/
def opFrameQ {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ∑ i, (c i : ℂ) • (B i ∘ₗ LinearMap.adjoint (B i))

section OperatorBridge

lemma toEuclideanLin_mul {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B :=
  Matrix.toLpLin_mul 2 2 2 A B

lemma toEuclideanLin_one {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.toEuclideanLin (1 : Matrix n n ℂ) = LinearMap.id :=
  Matrix.toLpLin_one 2

lemma toEuclideanLin_trace {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

lemma toEuclideanLin_adjoint {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

/-- Exact agreement between operator Hilbert–Schmidt norm and matrix `hsSq`. -/
theorem opHsSq_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    opHsSq (Matrix.toEuclideanLin A) = hsSq A := by
  unfold opHsSq
  rw [toEuclideanLin_adjoint, ← toEuclideanLin_mul, toEuclideanLin_trace, hsSq_eq_re]

theorem opFrameK_sub_id_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (c : ℝ) (A : Matrix m n ℂ) :
    opFrameK c (Matrix.toEuclideanLin A) - LinearMap.id =
      Matrix.toEuclideanLin ((c : ℂ) • (Aᴴ * A) - 1) := by
  unfold opFrameK
  rw [toEuclideanLin_adjoint, ← toEuclideanLin_mul, map_sub, map_smul, toEuclideanLin_one]

theorem opFrameQ_toEuclideanLin {ι : Type*} [Fintype ι] {D : ℕ} {d : ι → ℕ}
    (B : ∀ i, Matrix (Fin D) (Fin (d i)) ℂ) (ga : ι → ℝ) :
    opFrameQ ga (fun i => Matrix.toEuclideanLin (B i)) =
      Matrix.toEuclideanLin (frameOp B ga) := by
  unfold opFrameQ frameOp
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toEuclideanLin_mul, toEuclideanLin_adjoint]

end OperatorBridge

section OperatorCore

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

private lemma re_inner_self {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

omit [FiniteDimensional ℂ E] in
private lemma trace_eq_sum_inner_ob {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis κ ℂ E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E T = ∑ i, ⟪b i, T (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, Matrix.trace]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

lemma opHsSq_eq_basis_sum {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis κ ℂ E) :
    opHsSq A = ∑ m, ‖A (v m)‖ ^ 2 := by
  classical
  unfold opHsSq
  rw [trace_eq_sum_inner_ob v, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, re_inner_self]

lemma opHsSq_nonneg (A : E →ₗ[ℂ] F) : 0 ≤ opHsSq A := by
  rw [opHsSq_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sum_adj_norm_sq_eq {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis κ₁ ℂ E) (u : OrthonormalBasis κ₂ ℂ F) :
    ∑ n, ‖LinearMap.adjoint A (u n)‖ ^ 2 = ∑ m, ‖A (v m)‖ ^ 2 := by
  have h1 : ∀ n, ‖LinearMap.adjoint A (u n)‖ ^ 2 = ∑ m, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := fun n => by
    rw [← v.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.adjoint_inner_right, norm_inner_symm]
  have h2 : ∀ m, ‖A (v m)‖ ^ 2 = ∑ n, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 :=
    fun m => (u.sum_sq_norm_inner_right _).symm
  simp only [h1, h2]
  exact Finset.sum_comm

/-- Bessel inequality for Hilbert–Schmidt operators: for any orthonormal set `{g_l}`,
`∑_l ‖A g_l‖² ≤ ‖A‖_HS²`. -/
lemma sum_norm_sq_le_opHsSq {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F)
    {g : κ → E} (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ opHsSq A := by
  rw [opHsSq_eq_basis_sum A (stdOrthonormalBasis ℂ E),
    ← sum_adj_norm_sq_eq A (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F)]
  have h1 : ∀ l, ‖A (g l)‖ ^ 2 =
      ∑ n, ‖⟪g l, LinearMap.adjoint A (stdOrthonormalBasis ℂ F n)⟫_ℂ‖ ^ 2 := fun l => by
    rw [← (stdOrthonormalBasis ℂ F).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.adjoint_inner_right, norm_inner_symm]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun n _ => Orthonormal.sum_inner_products_le _ hg

lemma sum_re_inner_le_opHsSq {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] E)
    {g : κ → E} (hg : Orthonormal ℂ g) :
    |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (opHsSq A) := by
  have h1 : ∀ l, |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖A (g l)‖ := fun l => by
    calc |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖⟪g l, A (g l)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖g l‖ * ‖A (g l)‖ := norm_inner_le_norm _ _
      _ = ‖A (g l)‖ := by rw [hg.1 l, one_mul]
  have h2 : (∑ l, ‖A (g l)‖) ^ 2 ≤ (Fintype.card κ : ℝ) * opHsSq A := by
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ => (1 : ℝ)) (fun l => ‖A (g l)‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (sum_norm_sq_le_opHsSq A hg) (Nat.cast_nonneg _))
  calc |∑ l, (⟪g l, A (g l)⟫_ℂ).re|
      ≤ ∑ l, |(⟪g l, A (g l)⟫_ℂ).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ‖A (g l)‖ := Finset.sum_le_sum fun l _ => h1 l
    _ = Real.sqrt ((∑ l, ‖A (g l)‖) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card κ : ℝ) * opHsSq A) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (Fintype.card κ) * Real.sqrt (opHsSq A) := Real.sqrt_mul (Nat.cast_nonneg _) _

lemma frame_orthonormal_energy_bound (c : ℝ) (B : E →ₗ[ℂ] F) {κ : Type*} [Fintype κ]
    {g : κ → E} (hg : Orthonormal ℂ g) :
    |c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ|
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (opHsSq (opFrameK c B - LinearMap.id)) := by
  have h1 : ∀ l, (⟪g l, ((opFrameK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re =
      c * ‖B (g l)‖ ^ 2 - 1 := by
    intro l
    simp only [opFrameK, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply, inner_sub_right, inner_smul_right, LinearMap.adjoint_inner_right,
      Complex.sub_re, Complex.re_ofReal_mul, re_inner_self, hg.1 l]
    norm_num
  have h2 : ∑ l, (⟪g l, ((opFrameK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re =
      c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ := by
    rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  rw [← h2]
  exact sum_re_inner_le_opHsSq _ hg

end OperatorCore

section FrameDensityTheorem

variable {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

private lemma re_inner_opFrameQ (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, opFrameQ c B x⟫_ℂ).re = ∑ i, c i * ‖LinearMap.adjoint (B i) x‖ ^ 2 := by
  simp only [opFrameQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearMap.adjoint_inner_left (B i) (LinearMap.adjoint (B i) x) x, re_inner_self]

private lemma opFrameQ_symm (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x y : H) :
    ⟪opFrameQ c B x, y⟫_ℂ = ⟪x, opFrameQ c B y⟫_ℂ := by
  simp only [opFrameQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearMap.adjoint_inner_right (B i), LinearMap.adjoint_inner_left (B i)]

private lemma trace_opFrameQ_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (LinearMap.trace ℂ H (opFrameQ c B)).re =
      ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
  classical
  rw [trace_eq_sum_inner_ob (stdOrthonormalBasis ℂ H), Complex.re_sum]
  simp only [re_inner_opFrameQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum,
    sum_adj_norm_sq_eq (B i) (stdOrthonormalBasis ℂ (V i)) (stdOrthonormalBasis ℂ H)]

private lemma trace_opFrameQ_sq_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (LinearMap.trace ℂ H (opFrameQ c B ∘ₗ opFrameQ c B)).re =
      ∑ n, ‖opFrameQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by
  classical
  rw [trace_eq_sum_inner_ob (stdOrthonormalBasis ℂ H), Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.comp_apply, ← opFrameQ_symm, re_inner_self]

private lemma orth_energy_upper {V' H' : Type*}
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
    (B : V' →ₗ[ℂ] H') (N : Submodule ℂ V') {κ : Type*} [Fintype κ]
    {g : κ → H'} (hg : Orthonormal ℂ g) (horth : ∀ l, g l ∈ (N.map B)ᗮ) :
    ∑ l, ‖LinearMap.adjoint B (g l)‖ ^ 2 ≤
      ∑ m : Fin (Module.finrank ℂ Nᗮ), ‖B ((stdOrthonormalBasis ℂ Nᗮ m : Nᗮ) : V')‖ ^ 2 := by
  have hmem : ∀ l, LinearMap.adjoint B (g l) ∈ Nᗮ := fun l => by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [LinearMap.adjoint_inner_right]
    exact (Submodule.mem_orthogonal _ _).mp (horth l) (B v) (Submodule.mem_map_of_mem hv)
  let e := stdOrthonormalBasis ℂ Nᗮ
  have h1 : ∀ l, ‖LinearMap.adjoint B (g l)‖ ^ 2 =
      ∑ m, ‖⟪g l, B ((e m : Nᗮ) : V')⟫_ℂ‖ ^ 2 := fun l => by
    have hnorm : ‖(⟨LinearMap.adjoint B (g l), hmem l⟩ : Nᗮ)‖ = ‖LinearMap.adjoint B (g l)‖ := rfl
    rw [← hnorm, ← e.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun m _ => ?_
    change ‖⟪((e m : Nᗮ) : V'), LinearMap.adjoint B (g l)⟫_ℂ‖ ^ 2 = _
    rw [LinearMap.adjoint_inner_right, norm_inner_symm]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun m _ => Orthonormal.sum_inner_products_le _ hg

private lemma frame_density_algebra (D R w e ε η t X tW : ℝ)
    (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D)
    (ht : R * (1 - Real.sqrt e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - Real.sqrt w * Real.sqrt X ≤ tW)
    (hup : tW ≤ ε * R + R * Real.sqrt (ε * e)) :
    w ≤ (η + 4 * ε + 4 * Real.sqrt e) * D := by
  have hsw : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  have hse0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hse : Real.sqrt e ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRt : R ≤ 2 * t := by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 / D := le_trans hX0 hX
    have h2 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg h1 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    by_contra hneg
    push Not at hneg
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ η + 4 * ε + 4 * Real.sqrt e - 1) hD.le]
  push Not at hε4
  set q := Real.sqrt (ε * e)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ Real.sqrt e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * Real.sqrt X with hy
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [hy, mul_pow, div_pow, hsX]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]
  have hyt : y * t = D * Real.sqrt X := by rw [hy]; field_simp [htpos.ne']
  have hDt : D * (t / D) = t := by field_simp [hD.ne']
  have hkey : t * (w - Real.sqrt w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t / D * w - Real.sqrt w * Real.sqrt X ≤ R * (ε + q) := by linarith
    have h2 : t * w - D * (Real.sqrt w * Real.sqrt X) ≤ D * (R * (ε + q)) := by
      have := mul_le_mul_of_nonneg_left h1 hD.le
      have e1 : D * (t / D * w - Real.sqrt w * Real.sqrt X) =
          t * w - D * (Real.sqrt w * Real.sqrt X) := by
        linear_combination w * hDt
      linarith
    have h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      nlinarith
    have e2 : t * (Real.sqrt w * y) = D * (Real.sqrt w * Real.sqrt X) := by
      linear_combination Real.sqrt w * hyt
    nlinarith
  have hmain : w - Real.sqrt w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : Real.sqrt w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (Real.sqrt w - y)]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]

/-- **Sharp Inner-Product Frame-to-Corank Density Theorem** (`FrameLA1`):
Given a near-tight Bessel frame `{B_i : V_i → H}` with diagonal defect `≤ e`,
trace-square ratio `≤ 1 + η`, and subspaces `Nτ_i ≤ V_i` of total codimension share `≤ ε`,
the orthogonal complement `W = (⨆ i, (Nτ i).map (B i))ᗮ` has dimension at most
`(η + 4 * ε + 4 * √e) * finrank ℂ H`. -/
theorem frame_corank_density_bound
    (B : ∀ i, V i →ₗ[ℂ] H) (c : ι → ℝ) (Nτ : ∀ i, Submodule ℂ (V i)) (e η ε : ℝ)
    (hc : ∀ i, 0 < c i) (hd : 0 < ∑ i, Module.finrank ℂ (V i))
    (hK : (∑ i, opHsSq (opFrameK (c i) (B i) - LinearMap.id)) ≤
      e * ∑ i, (Module.finrank ℂ (V i) : ℝ))
    (he0 : 0 ≤ e) (he : e ≤ 1 / 4) (_hη : 0 ≤ η)
    (hQ : (LinearMap.trace ℂ H (opFrameQ c B ∘ₗ opFrameQ c B)).re ≤
      (1 + η) * (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ))
    (hN : (∑ i, ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i))) ≤
      ε * ∑ i, (Module.finrank ℂ (V i) : ℝ)) :
    (Module.finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ) ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Module.finrank ℂ H : ℝ) := by
  classical
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW
  have hwD : (Module.finrank ℂ W : ℝ) ≤ (Module.finrank ℂ H : ℝ) := by
    exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : Module.finrank ℂ H = 0
  · have h0 : Module.finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (Module.finrank ℂ H : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD0)
  have hR : 0 < ∑ i, (Module.finrank ℂ (V i) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (Module.finrank ℂ (Nτ i) : ℝ) ≤ Module.finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hKnn : 0 ≤ ∑ i, ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i)) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hnk i)
  have hε : 0 ≤ ε := by
    by_contra h
    push Not at h
    have : ε * ∑ i, (Module.finrank ℂ (V i) : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
    linarith
  -- Step 1: Lower bound on tr(Q)
  have hfull : ∀ i, (Module.finrank ℂ (V i) : ℝ) -
      Real.sqrt (Module.finrank ℂ (V i) : ℝ) *
        Real.sqrt (opHsSq (opFrameK (c i) (B i) - LinearMap.id)) ≤
      c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := fun i => by
    have h := frame_orthonormal_energy_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    linarith [(abs_le.mp h).1]
  have ht : (∑ i, (Module.finrank ℂ (V i) : ℝ)) * (1 - Real.sqrt e) ≤
      (LinearMap.trace ℂ H (opFrameQ c B)).re := by
    rw [trace_opFrameQ_eq]
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hfull i
    rw [Finset.sum_sub_distrib] at h1
    have hCS : ∑ i, Real.sqrt (Module.finrank ℂ (V i) : ℝ) *
        Real.sqrt (opHsSq (opFrameK (c i) (B i) - LinearMap.id)) ≤
        (∑ i, (Module.finrank ℂ (V i) : ℝ)) * Real.sqrt e := by
      calc _ ≤ Real.sqrt (∑ i, (Module.finrank ℂ (V i) : ℝ)) *
              Real.sqrt (∑ i, opHsSq (opFrameK (c i) (B i) - LinearMap.id)) :=
            sum_sqrt_mul_sqrt_le _ _ (fun _ => Nat.cast_nonneg _) (fun _ => opHsSq_nonneg _)
        _ ≤ Real.sqrt (∑ i, (Module.finrank ℂ (V i) : ℝ)) *
              Real.sqrt (e * ∑ i, (Module.finrank ℂ (V i) : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
        _ = (∑ i, (Module.finrank ℂ (V i) : ℝ)) * Real.sqrt e := by
            rw [Real.sqrt_mul he0]
            have hsq := Real.mul_self_sqrt hR.le
            linear_combination Real.sqrt e * hsq
    linarith
  -- Step 2: Upper bound on tr(Q|_W) via orthogonal complements Nτ_iᗮ
  let g : Fin (Module.finrank ℂ W) → H := fun l => (stdOrthonormalBasis ℂ W l : H)
  have hg : Orthonormal ℂ g :=
    ⟨fun l => (stdOrthonormalBasis ℂ W).orthonormal.1 l,
     fun i j hij => (stdOrthonormalBasis ℂ W).orthonormal.2 hij⟩
  set tW : ℝ := ∑ l, (⟪g l, opFrameQ c B (g l)⟫_ℂ).re with htWdef
  have htW : tW = ∑ i, c i * ∑ l, ‖LinearMap.adjoint (B i) (g l)‖ ^ 2 := by
    simp only [htWdef, re_inner_opFrameQ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hWi : ∀ i, c i * ∑ l, ‖LinearMap.adjoint (B i) (g l)‖ ^ 2 ≤
      ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i)) +
        Real.sqrt ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i)) *
          Real.sqrt (opHsSq (opFrameK (c i) (B i) - LinearMap.id)) := fun i => by
    have horth : ∀ l, g l ∈ ((Nτ i).map (B i))ᗮ := fun l =>
      Submodule.orthogonal_le (le_iSup (fun j => (Nτ j).map (B j)) i) (stdOrthonormalBasis ℂ W l).2
    have h1 := orth_energy_upper (B i) (Nτ i) hg horth
    let eN : Fin (Module.finrank ℂ (Nτ i)ᗮ) → V i := fun m => (stdOrthonormalBasis ℂ (Nτ i)ᗮ m : V i)
    have heN : Orthonormal ℂ eN :=
      ⟨fun m => (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.1 m,
       fun a b hab => (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.2 hab⟩
    have h2 := frame_orthonormal_energy_bound (c i) (B i) heN
    simp only [Fintype.card_fin] at h2
    have hk : (Module.finrank ℂ (Nτ i)ᗮ : ℝ) =
        (Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : Module.finrank ℂ (Nτ i)ᗮ + Module.finrank ℂ (Nτ i) =
        Module.finrank ℂ (V i))
    rw [hk] at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : tW ≤ ε * (∑ i, (Module.finrank ℂ (V i) : ℝ)) +
      (∑ i, (Module.finrank ℂ (V i) : ℝ)) * Real.sqrt (ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hWi i
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, Real.sqrt ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i)) *
        Real.sqrt (opHsSq (opFrameK (c i) (B i) - LinearMap.id)) ≤
        (∑ i, (Module.finrank ℂ (V i) : ℝ)) * Real.sqrt (ε * e) := by
      calc _ ≤ Real.sqrt (∑ i, ((Module.finrank ℂ (V i) : ℝ) - Module.finrank ℂ (Nτ i))) *
              Real.sqrt (∑ i, opHsSq (opFrameK (c i) (B i) - LinearMap.id)) :=
            sum_sqrt_mul_sqrt_le _ _ (fun i => sub_nonneg.mpr (hnk i)) (fun _ => opHsSq_nonneg _)
        _ ≤ Real.sqrt (ε * ∑ i, (Module.finrank ℂ (V i) : ℝ)) *
              Real.sqrt (e * ∑ i, (Module.finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = (∑ i, (Module.finrank ℂ (V i) : ℝ)) * Real.sqrt (ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (Module.finrank ℂ (V i) : ℝ)) * (e * ∑ i, (Module.finrank ℂ (V i) : ℝ))
                = ε * e * (∑ i, (Module.finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith
  -- Step 3: Lower bound on tr(Q|_W) via variance X = ‖Q - s I‖_HS²
  set s : ℝ := (LinearMap.trace ℂ H (opFrameQ c B)).re / (Module.finrank ℂ H : ℝ) with hs
  set A : H →ₗ[ℂ] H := opFrameQ c B - (s : ℂ) • LinearMap.id with hA
  have hlow : (LinearMap.trace ℂ H (opFrameQ c B)).re / (Module.finrank ℂ H : ℝ) *
      (Module.finrank ℂ W : ℝ) - Real.sqrt (Module.finrank ℂ W : ℝ) * Real.sqrt (opHsSq A) ≤ tW := by
    have h := sum_re_inner_le_opHsSq A hg
    simp only [Fintype.card_fin] at h
    have h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1 := fun l => by
      rw [inner_self_eq_norm_sq_to_K, hg.1 l]; simp
    have hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re = tW - s * (Module.finrank ℂ W : ℝ) := by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_sub_right, inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, htWdef]
      ring
    rw [hsum] at h
    linarith [(abs_le.mp h).1]
  have hX : opHsSq A ≤
      η * (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) := by
    set u := stdOrthonormalBasis ℂ H
    have hterm : ∀ n, ‖A (u n)‖ ^ 2 =
        ‖opFrameQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, opFrameQ c B (u n)⟫_ℂ).re + s ^ 2 := fun n => by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hsym : (⟪opFrameQ c B (u n), u n⟫_ℂ).re = (⟪u n, opFrameQ c B (u n)⟫_ℂ).re :=
        inner_re_symm (𝕜 := ℂ) _ _
      rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_one, sq_abs, hsym]
      ring
    have htr : (LinearMap.trace ℂ H (opFrameQ c B)).re =
        ∑ n, (⟪u n, opFrameQ c B (u n)⟫_ℂ).re := by
      rw [trace_eq_sum_inner_ob u, Complex.re_sum]
    have hT2 := trace_opFrameQ_sq_eq c B
    rw [opHsSq_eq_basis_sum _ u]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htr, ← hT2]
    have hsD : s * (Module.finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (opFrameQ c B)).re := by
      rw [hs]; field_simp [hD.ne']
    have hst : (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) =
        s * (LinearMap.trace ℂ H (opFrameQ c B)).re := by
      rw [hs]; field_simp [hD.ne']
    have hDs2 : (Module.finrank ℂ H : ℝ) * s ^ 2 =
        s * (LinearMap.trace ℂ H (opFrameQ c B)).re := by
      rw [← hsD]; ring
    have hQ' : (LinearMap.trace ℂ H (opFrameQ c B ∘ₗ opFrameQ c B)).re ≤
        (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) +
          η * (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) := by
      have heq : (1 + η) * (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) =
          (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) +
            η * (LinearMap.trace ℂ H (opFrameQ c B)).re ^ 2 / (Module.finrank ℂ H : ℝ) := by ring
      linarith
    linarith
  exact frame_density_algebra _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (opHsSq_nonneg _) hX hlow hup

end FrameDensityTheorem

section ProjectedAmbientCorank

/-- **Projected Ambient Dual-Lattice Corank Bound** (`thmF_place` abstraction):
If `Ball_i : ℂ^{d_i} → ℂ^{κ ⊕ κ₁}` satisfies the frame bounds `(e, η)` and projects via the
coordinate projection `P : ℂ^{κ ⊕ κ₁} → ℂ^κ` into a target subspace `T ≤ ℂ^κ`, with
`(1 - δ) * |κ ⊕ κ₁| ≤ |κ|`, then the codimension of `T` in `ℂ^κ` satisfies:
`|κ| - finrank T ≤ (1 - δ)⁻¹ * (η + 4 * ε + 4 * √e) * |κ|`. -/
theorem projected_ambient_corank_bound
    {ι κ κ₁ : Type*} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    {d : ι → ℕ}
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (Fin (d i)) ℂ) (c : ι → ℝ)
    (Nτ : ∀ i, Submodule ℂ (EuclideanSpace ℂ (Fin (d i))))
    (T : Submodule ℂ (EuclideanSpace ℂ κ)) (e η ε δ : ℝ)
    (hc : ∀ i, 0 < c i) (hpos : 0 < ∑ i, d i)
    (hF2 : ∑ i, opHsSq (opFrameK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id) ≤
      e * ∑ i, (d i : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
          opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (opFrameQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hcor : ∑ i, ((d i : ℝ) - Module.finrank ℂ (Nτ i)) ≤ ε * ∑ i, (d i : ℝ))
    (hδ1 : δ < 1)
    (hcard : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (hproj : ∀ i (v : EuclideanSpace ℂ (Fin (d i))), v ∈ Nτ i →
      (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin (Ball i) v) (Sum.inl k)) ∈ T) :
    (Fintype.card κ : ℝ) - Module.finrank ℂ T ≤
      (1 - δ)⁻¹ * (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card κ : ℝ) := by
  classical
  let eqK : (κ → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ κ := (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
  let eqKK1 : (κ ⊕ κ₁ → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (κ ⊕ κ₁) :=
    (WithLp.linearEquiv 2 ℂ (κ ⊕ κ₁ → ℂ)).symm
  let P : EuclideanSpace ℂ (κ ⊕ κ₁) →ₗ[ℂ] EuclideanSpace ℂ κ :=
    eqK.toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ Sum.inl ∘ₗ eqKK1.symm.toLinearMap
  have hPsurj : LinearMap.range P = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨eqKK1 (Sum.elim (eqK.symm y) 0), ?_⟩
    ext k
    simp [P, eqK, eqKK1, LinearMap.funLeft]
  have hkerP : Module.finrank ℂ (LinearMap.ker P) = Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker P
    rw [hPsurj, finrank_top, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at h
    omega
  let Ba : ∀ i, EuclideanSpace ℂ (Fin (d i)) →ₗ[ℂ] EuclideanSpace ℂ (κ ⊕ κ₁) :=
    fun i => Matrix.toEuclideanLin (Ball i)
  let S : Submodule ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) := ⨆ i, (Nτ i).map (Ba i)
  have hPS : S.map P ≤ T := by
    simp only [S, Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact hproj i v hv
  have hSdim : Module.finrank ℂ S ≤ Module.finrank ℂ (S.map P) + Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (P ∘ₗ S.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    have hk : Module.finrank ℂ (LinearMap.ker (P ∘ₗ S.subtype)) ≤
        Module.finrank ℂ (LinearMap.ker P) := by
      rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq]
      exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
    omega
  have hLA := frame_corank_density_bound Ba c Nτ e η ε hc
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; exact hpos)
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; exact hF2)
    he0 he1 hη
    (by simp only [finrank_euclideanSpace]; exact hF1)
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; exact hcor)
  rw [finrank_euclideanSpace] at hLA
  have hsum : (Module.finrank ℂ S : ℝ) + (Module.finrank ℂ Sᗮ : ℝ) =
      (Fintype.card κ : ℝ) + Fintype.card κ₁ := by
    have h := Submodule.finrank_add_finrank_orthogonal S
    rw [finrank_euclideanSpace, Fintype.card_sum] at h
    exact_mod_cast h
  have hmono : (Module.finrank ℂ (S.map P) : ℝ) ≤ Module.finrank ℂ T :=
    Nat.cast_le.mpr (Submodule.finrank_mono hPS)
  have hSdim' : (Module.finrank ℂ S : ℝ) ≤ Module.finrank ℂ (S.map P) + Fintype.card κ₁ := by
    exact_mod_cast hSdim
  have hbase : (Fintype.card κ : ℝ) - Module.finrank ℂ T ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by
    linarith
  have h1m : 0 < 1 - δ := by linarith
  have hcard' : (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (1 - δ)⁻¹ * (Fintype.card κ : ℝ) := by
    rw [← div_eq_inv_mul, le_div_iff₀ h1m]
    linarith
  have hcoeff_nn : 0 ≤ η + 4 * ε + 4 * Real.sqrt e := by
    have hR : 0 < ∑ i, (d i : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hpos
    have hKnn : 0 ≤ ∑ i, ((d i : ℝ) - Module.finrank ℂ (Nτ i)) := Finset.sum_nonneg fun i _ => by
      have : Module.finrank ℂ (Nτ i) ≤ d i := by
        simpa [finrank_euclideanSpace] using Submodule.finrank_le (Nτ i)
      exact sub_nonneg.mpr (Nat.cast_le.mpr this)
    have hε0 : 0 ≤ ε := by
      by_contra h; push Not at h
      have : ε * ∑ i, (d i : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
      linarith
    positivity
  calc (Fintype.card κ : ℝ) - Module.finrank ℂ T
      ≤ (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := hbase
    _ ≤ (η + 4 * ε + 4 * Real.sqrt e) * ((1 - δ)⁻¹ * (Fintype.card κ : ℝ)) :=
        mul_le_mul_of_nonneg_left hcard' hcoeff_nn
    _ = (1 - δ)⁻¹ * (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card κ : ℝ) := by ring

/-- **End-to-End Gram-Input + Isometric Compression → Ambient Dual-Lattice Corank Bound**:
Directly combines `compress_trace_square_bound`, `compress_diag_defect_bound`,
the matrix-to-Euclidean bridge, and `projected_ambient_corank_bound`! -/
theorem projected_gram_corank_density_bound
    {ι κ κ₁ : Type*} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    {d r : ι → ℕ}
    (Bf : ∀ i, Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (d i)) ℂ)
    (Vr : ∀ i, Matrix (Fin (d i)) (Fin (r i)) ℂ)
    (ga : ι → ℝ)
    (Nτ : ∀ i, Submodule ℂ (EuclideanSpace ℂ (Fin (r i))))
    (T : Submodule ℂ (EuclideanSpace ℂ κ))
    (Dstar sg η0 η1 e0 de ε δ : ℝ)
    (hV : IsIsometryFamily Vr) (hga : ∀ i, 0 < ga i)
    (hDs : 0 < Dstar) (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20)
    (hR : Dstar / sg ≤ totalRank d)
    (hη0 : -1 ≤ η0) (hη0' : η0 ≤ sg / 2) (hη1 : η1 ≤ sg / 2)
    (he0 : 0 ≤ e0) (hse : Real.sqrt e0 ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4)
    (hcorV : ∑ i, ((d i : ℝ) - (r i : ℝ)) ≤ de * totalRank d)
    (hS : GramInput Bf ga Dstar η0 η1 e0)
    (hcorN : ∑ i, ((r i : ℝ) - Module.finrank ℂ (Nτ i)) ≤ ε * ∑ i, (r i : ℝ))
    (hδ1 : δ < 1)
    (hcard : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (hproj : ∀ i (v : EuclideanSpace ℂ (Fin (r i))), v ∈ Nτ i →
      (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
            (compressFamily Bf Vr i)) v) (Sum.inl k)) ∈ T) :
    (Fintype.card κ : ℝ) - Module.finrank ℂ T ≤
      (1 - δ)⁻¹ * ((5 * sg + 3 * Real.sqrt de) + 4 * ε + 4 * Real.sqrt (2 * e0)) *
        (Fintype.card κ : ℝ) := by
  classical
  have hga0 : ∀ i, 0 ≤ ga i := fun i => (hga i).le
  have hF1_mat := compress_trace_square_bound Bf Vr ga Dstar sg η0 η1 e0 de
    hV hga0 hDs hsg hsg20 hR hη0 hη0' hη1 he0 hse hde0 hde4 hcorV hS
  obtain ⟨hRr, hF2_mat⟩ := compress_diag_defect_bound Bf Vr ga de e0
    hV (by linarith) he0 hS.2.1 hcorV
  have hRpos : 0 < totalRank d := lt_of_lt_of_le (div_pos hDs hsg) hR
  have hpos_r : 0 < ∑ i, r i := by
    have h1 : 0 < totalRank r := lt_of_lt_of_le (mul_pos (by linarith) hRpos) hRr
    unfold totalRank at h1
    rw [← Nat.cast_sum] at h1
    exact_mod_cast h1
  let e_idx := (Fintype.equivFin (κ ⊕ κ₁)).symm
  let Ball : ∀ i, Matrix (κ ⊕ κ₁) (Fin (r i)) ℂ :=
    fun i => Matrix.reindex e_idx (Equiv.refl _) (compressFamily Bf Vr i)
  have hKeq : ∀ i, opHsSq (opFrameK (ga i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id) =
      hsSq (gramDiag (compressFamily Bf Vr) ga i - 1) := fun i => by
    rw [opFrameK_sub_id_toEuclideanLin, opHsSq_toEuclideanLin,
      gramDiag_eq (compressFamily Bf Vr) ga hga0 i]
    have hmul : (Ball i)ᴴ * Ball i = (compressFamily Bf Vr i)ᴴ * compressFamily Bf Vr i := by
      ext a b
      simp only [Ball, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl]
      exact e_idx.symm.sum_comp fun j =>
        star (compressFamily Bf Vr i j a) * compressFamily Bf Vr i j b
    rw [hmul]
  have hF2 : ∑ i, opHsSq (opFrameK (ga i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id) ≤
      (2 * e0) * ∑ i, (r i : ℝ) := by
    simp only [hKeq]; exact hF2_mat
  have hQ_reindex : (∑ i, ((ga i : ℝ) : ℂ) • (Ball i * (Ball i)ᴴ)) =
      Matrix.reindex e_idx e_idx (frameOp (compressFamily Bf Vr) ga) := by
    unfold frameOp
    ext a b
    simp only [Ball, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.refl_symm, Equiv.coe_refl, id_eq]
  have hQ_lin : opFrameQ ga (fun i => Matrix.toEuclideanLin (Ball i)) =
      Matrix.toEuclideanLin (Matrix.reindex e_idx e_idx (frameOp (compressFamily Bf Vr) ga)) := by
    rw [← hQ_reindex]
    unfold opFrameQ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, toEuclideanLin_mul, toEuclideanLin_adjoint]
  have htr_re : ∀ (M : Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (Fintype.card (κ ⊕ κ₁))) ℂ),
      (Matrix.reindex e_idx e_idx M).trace = M.trace := fun M => by
    unfold Matrix.trace
    exact e_idx.symm.sum_comp fun j => M j j
  have hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
      (opFrameQ ga (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
        opFrameQ ga (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + (5 * sg + 3 * Real.sqrt de)) *
        (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
          (opFrameQ ga (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) := by
    rw [hQ_lin, ← toEuclideanLin_mul, toEuclideanLin_trace, toEuclideanLin_trace]
    have hmul : Matrix.reindex e_idx e_idx (frameOp (compressFamily Bf Vr) ga) *
        Matrix.reindex e_idx e_idx (frameOp (compressFamily Bf Vr) ga) =
        Matrix.reindex e_idx e_idx
          (frameOp (compressFamily Bf Vr) ga * frameOp (compressFamily Bf Vr) ga) := by
      simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [hmul, htr_re, htr_re]
    exact hF1_mat
  have he4 : 2 * e0 ≤ 1 / 4 := by
    have hsq := Real.sq_sqrt he0
    have hnn := Real.sqrt_nonneg e0
    nlinarith
  exact projected_ambient_corank_bound Ball ga Nτ T (2 * e0) (5 * sg + 3 * Real.sqrt de) ε δ
    hga hpos_r hF2 (by positivity) he4 (by positivity) hF1 hcorN hδ1 hcard hproj

end ProjectedAmbientCorank

end InnerProductFrame

/-! ## Section 4: Corank-Share, Layer-Cake Integration & `RHDirect.BostSlopeFiber.SlopeIneq` -/

section CorankShareAndLayerCake

/-- **Corank-Share Tail Inequality** (`CorankShare` / `thmF_share`):
For a finite family of values `x i j ≤ s + u` (`u ≥ 0`) with average `≥ s`, the total number
of indices falling below `s - τ` (`τ ≥ 0`) is at most `(∑ i, m i) * (u / (u + τ))`. -/
theorem corank_share_bound {I : Type*} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ)
    (s u τ : ℝ) (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((Finset.univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤
      (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  classical
  rcases lt_or_eq_of_le hu with hu' | rfl
  · set K := ∑ i, ((Finset.univ.filter (fun j => x i j < s - τ)).card : ℝ)
    set R := ∑ i, (m i : ℝ)
    have hup : 0 < u + τ := by linarith
    have hpt : ∀ i, ∑ j : Fin (m i), x i j ≤
        ((Finset.univ.filter (fun j => x i j < s - τ)).card : ℝ) * (s - τ) +
          ((m i : ℝ) - ((Finset.univ.filter (fun j => x i j < s - τ)).card : ℝ)) * (s + u) := by
      intro i
      set S := Finset.univ.filter (fun j : Fin (m i) => x i j < s - τ)
      have hsplit : ∑ j : Fin (m i), x i j = (∑ j ∈ S, x i j) + ∑ j ∈ Sᶜ, x i j := by
        rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
      have h1 : ∑ j ∈ S, x i j ≤ (S.card : ℝ) * (s - τ) := by
        calc ∑ j ∈ S, x i j ≤ ∑ _j ∈ S, (s - τ) :=
              Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.le
          _ = (S.card : ℝ) * (s - τ) := by rw [Finset.sum_const, nsmul_eq_mul]
      have hScard : (Sᶜ.card : ℝ) = (m i : ℝ) - (S.card : ℝ) := by
        have h := Finset.card_compl S
        rw [Fintype.card_fin] at h
        have hle' : S.card ≤ m i := by
          calc S.card ≤ (Finset.univ : Finset (Fin (m i))).card := Finset.card_filter_le _ _
            _ = m i := Fintype.card_fin _
        rw [h, Nat.cast_sub hle']
      have h2 : ∑ j ∈ Sᶜ, x i j ≤ ((m i : ℝ) - (S.card : ℝ)) * (s + u) := by
        calc ∑ j ∈ Sᶜ, x i j ≤ ∑ _j ∈ Sᶜ, (s + u) :=
              Finset.sum_le_sum fun j _ => hle i j
          _ = (Sᶜ.card : ℝ) * (s + u) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((m i : ℝ) - (S.card : ℝ)) * (s + u) := by rw [hScard]
      linarith
    have htot : ∑ i, ∑ j, x i j ≤ K * (s - τ) + (R - K) * (s + u) := by
      have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib] at h
      exact h
    have hmul : K * (u + τ) ≤ R * u := by linarith
    rw [mul_div_assoc', le_div_iff₀ hup]
    linarith
  · have hempty : ∀ i, Finset.univ.filter (fun j => x i j < s - τ) = ∅ := by
      intro i
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hj' := (Finset.mem_filter.1 hj).2
      have hlt : ∑ i', ∑ j', x i' j' < ∑ i', ∑ _j' : Fin (m i'), s := by
        apply Finset.sum_lt_sum
        · intro i' _
          exact Finset.sum_le_sum fun j' _ => by linarith [hle i' j']
        · exact ⟨i, Finset.mem_univ _, Finset.sum_lt_sum (fun j' _ => by linarith [hle i j'])
            ⟨j, Finset.mem_univ _, by linarith⟩⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      rw [Finset.sum_mul] at hsum
      linarith
    simp [hempty]

private lemma ind_lt_antitone (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) := by
  intro a b hab
  show (if b < c then (1 : ℝ) else 0) ≤ (if a < c then (1 : ℝ) else 0)
  by_cases h1 : b < c
  · simp [h1, lt_of_le_of_lt hab h1]
  · by_cases h2 : a < c <;> simp [h1, h2]

private lemma ind_lt_integral (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, (if τ < c then (1 : ℝ) else 0) = c := by
  have hi1 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) volume 0 c :=
    (ind_lt_antitone c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) volume c HH :=
    (ind_lt_antitone c).intervalIntegrable
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by rw [ae_iff]; simp
  have h1 : ∫ τ in (0 : ℝ)..c, (if τ < c then (1 : ℝ) else 0) = ∫ _τ in (0 : ℝ)..c, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hc0] at hmem
    simp [lt_of_le_of_ne hmem.2 hx]
  have h2 : ∫ τ in c..HH, (if τ < c then (1 : ℝ) else 0) = ∫ _τ in c..HH, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    simp [not_lt.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  simp

/-- **Layer-Cake Integral Inequality** (`LayerCake`):
If `a - HH ≤ x j` for all `j : Fin D` and the tail count `#{j | x j < a - τ}` is bounded by
`w τ * D` for all `τ ∈ [0, HH]`, then `a - ∫ τ in 0..HH, min 1 (w τ) ≤ (∑ j, x j) / D`. -/
theorem layer_cake_bound (D : ℕ) (x : Fin D → ℝ) (a HH : ℝ) (w : ℝ → ℝ)
    (hD : 0 < D) (hHH : 0 ≤ HH) (hx : ∀ j, a - HH ≤ x j)
    (hw : IntervalIntegrable (fun τ => min 1 (w τ)) volume 0 HH)
    (hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < a - τ)).card : ℝ) ≤ w τ * D) :
    a - (∫ τ in (0 : ℝ)..HH, min 1 (w τ)) ≤ (∑ j, x j) / D := by
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hcount : ∀ τ : ℝ, ∑ j, (if τ < a - x j then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) := fun τ => by
    rw [Finset.sum_boole]
    exact congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card
      (Finset.filter_congr fun j _ => by constructor <;> intro hh <;> linarith))
  have hanti : Antitone (fun τ : ℝ => ∑ j, (if τ < a - x j then (1 : ℝ) else 0)) :=
    fun _ _ ht => Finset.sum_le_sum fun j _ => ind_lt_antitone (a - x j) ht
  have hint : ∫ τ in (0 : ℝ)..HH, ∑ j, (if τ < a - x j then (1 : ℝ) else 0) =
      ∑ j, ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) :=
    intervalIntegral.integral_finsetSum fun j _ => (ind_lt_antitone (a - x j)).intervalIntegrable
  have hlb : ∀ j, a - x j ≤ ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) := fun j => by
    rcases le_total (a - x j) 0 with h0 | h0
    · have hpos : 0 ≤ ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) :=
        intervalIntegral.integral_nonneg hHH fun _ _ => by split_ifs <;> norm_num
      linarith
    · exact le_of_eq (ind_lt_integral (a - x j) HH h0 (by linarith [hx j])).symm
  have hsum : ∑ j, (a - x j) ≤ ∑ j, ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => hlb j
  have hL : ∑ j, (a - x j) = (D : ℝ) * a - ∑ j, x j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmono : ∫ τ in (0 : ℝ)..HH, ∑ j, (if τ < a - x j then (1 : ℝ) else 0) ≤
      ∫ τ in (0 : ℝ)..HH, (D : ℝ) * min 1 (w τ) := by
    apply intervalIntegral.integral_mono_on hHH hanti.intervalIntegrable (hw.const_mul (D : ℝ))
    intro τ hτ
    rw [hcount τ]
    have hc1 : ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) ≤ D := by
      have : (Finset.univ.filter fun j => x j < a - τ).card ≤ D :=
        (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin D)
      exact_mod_cast this
    have hc2 := hcnt τ hτ
    rcases le_total 1 (w τ) with hw1 | hw1
    · rw [min_eq_left hw1]; linarith
    · rw [min_eq_right hw1]; linarith
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [le_div_iff₀ hDpos]
  linarith

/-- Exact analytic integral of the corank-share density profile:
`∫ τ in 0..HH, (4 * u / (u + τ) + c) = 4 * u * Real.log (1 + HH / u) + c * HH`. -/
theorem integral_four_u_div (u HH c : ℝ) (hu : 0 < u) (hHH : 0 ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, (4 * u / (u + τ) + c) = 4 * u * Real.log (1 + HH / u) + c * HH := by
  have hF : ∀ τ ∈ Set.uIcc (0 : ℝ) HH,
      HasDerivAt (fun t => 4 * u * Real.log (u + t) + c * t) (4 * u / (u + τ) + c) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le hHH] at hτ
    have hpos : u + τ ≠ 0 := by linarith [hτ.1]
    have h1 : HasDerivAt (fun t : ℝ => u + t) 1 τ := (hasDerivAt_id' τ).const_add u
    have h2 : HasDerivAt (fun t : ℝ => Real.log (u + t)) (1 / (u + τ)) τ := by
      simpa [one_div] using h1.log hpos
    have h3 : HasDerivAt (fun t : ℝ => 4 * u * Real.log (u + t)) (4 * u * (1 / (u + τ))) τ :=
      h2.const_mul (4 * u)
    have h4 : HasDerivAt (fun t : ℝ => c * t) (c * 1) τ := (hasDerivAt_id' τ).const_mul c
    have hsum : HasDerivAt (fun t : ℝ => 4 * u * Real.log (u + t) + c * t)
        (4 * u * (1 / (u + τ)) + c * 1) τ := h3.add h4
    rwa [show 4 * u * (1 / (u + τ)) + c * 1 = 4 * u / (u + τ) + c by ring] at hsum
  have hcont : ContinuousOn (fun τ => 4 * u / (u + τ) + c) (Set.uIcc (0 : ℝ) HH) := by
    refine ContinuousOn.add (ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuousOn_id) ?_) continuousOn_const
    intro τ hτ
    rw [Set.uIcc_of_le hHH] at hτ
    linarith [hτ.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  have hlog : Real.log (u + HH) - Real.log u = Real.log (1 + HH / u) := by
    rw [← Real.log_div (by linarith) hu.ne']
    congr 1
    field_simp [hu.ne']
  have hsub : 4 * u * Real.log (u + HH) + c * HH - (4 * u * Real.log (u + 0) + c * 0) =
      4 * u * (Real.log (u + HH) - Real.log u) + c * HH := by rw [add_zero]; ring
  rw [hsub, hlog]

/-- **Direct Deduction of `RHDirect.BostSlopeFiber.SlopeIneq` from Corank Density**:
Given ambient Harder–Narasimhan slopes `x : Fin D → ℝ` with average `muCC = (∑ j, x j) / D`,
lower bound `muMinCC ≤ x j`, and corank tail density bound
`#{j | x j < s - log |W| - τ} ≤ (1 - del)⁻¹ * (η + 4 * (uF / (uF + τ)) + 4 * √e) * D`,
the fiber `B : BostSlopeFiber` satisfies `B.SlopeIneq`! -/
theorem bost_slope_ineq_of_corank_density (B : RHDirect.BostSlopeFiber)
    (D : ℕ) (hD : 0 < D) (x : Fin D → ℝ)
    (huF : 0 < B.uF) (hcardW : 1 ≤ B.cardW)
    (hAvg : (∑ j, x j) / D = B.muCC)
    (hMin : ∀ j, B.muMinCC ≤ x j)
    (hTail : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
      ((Finset.univ.filter (fun j => x j < B.s - Real.log (B.cardW : ℝ) - τ)).card : ℝ) ≤
        (1 - B.del)⁻¹ * (B.η + 4 * (B.uF / (B.uF + τ)) + 4 * Real.sqrt B.e) * D) :
    B.SlopeIneq := by
  intro hdel0 hdel1 hη0 he0 _he4 hHH_ge hHH_pos
  have hlogW : 0 ≤ Real.log (B.cardW : ℝ) := Real.log_nonneg (by exact_mod_cast hcardW)
  have hx : ∀ j, (B.s - Real.log (B.cardW : ℝ)) - B.HH ≤ x j := fun j => by
    linarith [hMin j]
  let w : ℝ → ℝ := fun τ => (1 - B.del)⁻¹ * (4 * B.uF / (B.uF + τ) + (B.η + 4 * Real.sqrt B.e))
  have hw_cont : ContinuousOn w (Set.uIcc (0 : ℝ) B.HH) := by
    refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.add (ContinuousOn.div continuousOn_const
        (continuousOn_const.add continuousOn_id) ?_) continuousOn_const)
    intro τ hτ
    rw [Set.uIcc_of_le hHH_pos.le] at hτ
    linarith [hτ.1]
  have hw_int : IntervalIntegrable w volume 0 B.HH := hw_cont.intervalIntegrable
  have hmin_anti : AntitoneOn (fun τ => min 1 (w τ)) (Set.uIcc (0 : ℝ) B.HH) := by
    intro a ha b hb hab
    rw [Set.uIcc_of_le hHH_pos.le] at ha hb
    refine min_le_min_left 1 ?_
    have hinv_nn : 0 ≤ (1 - B.del)⁻¹ := inv_nonneg.mpr (by linarith)
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hinv_nn
    exact div_le_div_of_nonneg_left (by positivity) (by linarith [ha.1]) (by linarith)
  have hmin_int : IntervalIntegrable (fun τ => min 1 (w τ)) volume 0 B.HH :=
    hmin_anti.intervalIntegrable
  have hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
      ((Finset.univ.filter (fun j => x j < (B.s - Real.log (B.cardW : ℝ)) - τ)).card : ℝ) ≤
        w τ * D := fun τ hτ => by
    have h := hTail τ hτ
    have heq : w τ = (1 - B.del)⁻¹ * (B.η + 4 * (B.uF / (B.uF + τ)) + 4 * Real.sqrt B.e) := by
      dsimp only [w]; ring
    rwa [heq]
  have hlc := layer_cake_bound D x (B.s - Real.log (B.cardW : ℝ)) B.HH w hD hHH_pos.le
    hx hmin_int hcnt
  rw [hAvg] at hlc
  have hmin_le : ∫ τ in (0 : ℝ)..B.HH, min 1 (w τ) ≤ ∫ τ in (0 : ℝ)..B.HH, w τ :=
    intervalIntegral.integral_mono_on hHH_pos.le hmin_int hw_int fun _ _ => min_le_right _ _
  have hint_w : ∫ τ in (0 : ℝ)..B.HH, w τ =
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) := by
    dsimp only [w]
    rw [intervalIntegral.integral_const_mul,
      integral_four_u_div B.uF B.HH (B.η + 4 * Real.sqrt B.e) huF hHH_pos.le]
  linarith

/-- **Full End-to-End Gram-Matrix + Compression + Corank-Share + Layer-Cake ⇒ `BostSlopeFiber.SlopeIneq`**:
Packages the entire dual-lattice frame pipeline: given `GramInput` on `Bf` with isometry `Vr`,
slopes `y i j ≤ s + uF` of mean `≥ s`, and ambient subspaces `T τ` capturing the `τ`-threshold
subspaces with codimension matching `#{j | x j < s - log |W| - τ}`, deduce `B.SlopeIneq` with
`η = 5 * sg + 3 * √de` and `e = 2 * e0`! -/
theorem bost_slope_ineq_of_gram_input
    {ι κ κ₁ : Type*} [Fintype ι] [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁]
    {d r : ι → ℕ}
    (Bf : ∀ i, Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (d i)) ℂ)
    (Vr : ∀ i, Matrix (Fin (d i)) (Fin (r i)) ℂ)
    (ga : ι → ℝ)
    (Dstar sg η0 η1 e0 de δ s uF HH muMinCC muCC : ℝ) (cardW : ℕ)
    (hV : IsIsometryFamily Vr) (hga : ∀ i, 0 < ga i)
    (hDs : 0 < Dstar) (hsg : 0 < sg) (hsg20 : sg ≤ 1 / 20)
    (hR : Dstar / sg ≤ totalRank d)
    (hη0 : -1 ≤ η0) (hη0' : η0 ≤ sg / 2) (hη1 : η1 ≤ sg / 2)
    (he0 : 0 ≤ e0) (hse : Real.sqrt e0 ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4)
    (hcorV : ∑ i, ((d i : ℝ) - (r i : ℝ)) ≤ de * totalRank d)
    (hS : GramInput Bf ga Dstar η0 η1 e0)
    (hδ1 : δ < 1)
    (hcard : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ))
    (hκpos : 0 < Fintype.card κ) (huF : 0 < uF) (hcardW : 1 ≤ cardW)
    -- Source slopes and ambient slopes
    (y : ∀ i, Fin (r i) → ℝ)
    (hy_mean : (∑ i, (r i : ℝ)) * s ≤ ∑ i, ∑ j, y i j)
    (hy_top : ∀ i j, y i j ≤ s + uF)
    (x : Fin (Fintype.card κ) → ℝ)
    (hx_avg : (∑ j, x j) / (Fintype.card κ : ℝ) = muCC)
    (hx_min : ∀ j, muMinCC ≤ x j)
    -- For each τ ∈ [0, HH], threshold subspaces Nτ_i and ambient target T_τ
    (Nτ : ℝ → ∀ i, Submodule ℂ (EuclideanSpace ℂ (Fin (r i))))
    (T : ℝ → Submodule ℂ (EuclideanSpace ℂ κ))
    (hNτ_corank : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ i,
      (r i : ℝ) - Module.finrank ℂ (Nτ τ i) ≤
        ((Finset.univ.filter (fun j => y i j < s - τ)).card : ℝ))
    (hT_proj : ∀ τ ∈ Set.Icc (0 : ℝ) HH, ∀ i (v : EuclideanSpace ℂ (Fin (r i))), v ∈ Nτ τ i →
      (WithLp.linearEquiv 2 ℂ (κ → ℂ)).symm
        (fun k => (Matrix.toEuclideanLin
          (Matrix.reindex (Fintype.equivFin (κ ⊕ κ₁)).symm (Equiv.refl _)
            (compressFamily Bf Vr i)) v) (Sum.inl k)) ∈ T τ)
    (hT_tail : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter (fun j => x j < s - Real.log (cardW : ℝ) - τ)).card : ℝ) ≤
        (Fintype.card κ : ℝ) - Module.finrank ℂ (T τ)) :
    ({ del := δ
       η := 5 * sg + 3 * Real.sqrt de
       e := 2 * e0
       s := s
       muMinCC := muMinCC
       muCC := muCC
       HH := HH
       uF := uF
       cardW := cardW } : RHDirect.BostSlopeFiber).SlopeIneq := by
  refine bost_slope_ineq_of_corank_density _ (Fintype.card κ) hκpos x huF hcardW hx_avg hx_min ?_
  intro τ hτ
  have hshare := corank_share_bound r y s uF τ huF.le hτ.1 hy_mean hy_top
  have hcorN : ∑ i, ((r i : ℝ) - Module.finrank ℂ (Nτ τ i)) ≤
      (uF / (uF + τ)) * ∑ i, (r i : ℝ) := by
    calc ∑ i, ((r i : ℝ) - Module.finrank ℂ (Nτ τ i))
        ≤ ∑ i, ((Finset.univ.filter (fun j => y i j < s - τ)).card : ℝ) :=
          Finset.sum_le_sum fun i _ => hNτ_corank τ hτ i
      _ ≤ (∑ i, (r i : ℝ)) * (uF / (uF + τ)) := hshare
      _ = (uF / (uF + τ)) * ∑ i, (r i : ℝ) := mul_comm _ _
  have hbound := projected_gram_corank_density_bound Bf Vr ga (Nτ τ) (T τ)
    Dstar sg η0 η1 e0 de (uF / (uF + τ)) δ
    hV hga hDs hsg hsg20 hR hη0 hη0' hη1 he0 hse hde0 hde4 hcorV hS
    hcorN hδ1 hcard (hT_proj τ hτ)
  exact le_trans (hT_tail τ hτ) hbound

/-! ## Section 5: Monotonicity & Slope-Window Collapse (`PhiMonotonicityLemmas`) -/

/-- The Bost logarithmic spread profile `φ_H(u) = u * log (1 + H / u)`. -/
def phi (H u : ℝ) : ℝ := u * Real.log (1 + H / u)

/-- `φ_H(u)` is monotone in `u ≥ 0` for `H ≥ 0`. -/
theorem phi_mono {H u₁ u₂ : ℝ} (hH : 0 ≤ H) (hu1 : 0 < u₁) (hu12 : u₁ ≤ u₂) :
    phi H u₁ ≤ phi H u₂ := by
  have hu2 : 0 < u₂ := lt_of_lt_of_le hu1 hu12
  have hderiv : ∀ u ∈ Set.Icc u₁ u₂,
      HasDerivAt (fun t => t * Real.log (1 + H / t))
        (Real.log (1 + H / u) - H / (u + H)) u := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le hu1 hu.1
    have h1 : HasDerivAt (fun t : ℝ => 1 + H / t) (-H / u ^ 2) u := by
      have hd : HasDerivAt (fun t : ℝ => H / t) ((0 * u - H * 1) / u ^ 2) u :=
        (hasDerivAt_const u H).div (hasDerivAt_id' u) hu_pos.ne'
      have hadd : HasDerivAt (fun t : ℝ => 1 + H / t) ((0 * u - H * 1) / u ^ 2) u :=
        hd.const_add 1
      rwa [show (0 * u - H * 1) / u ^ 2 = -H / u ^ 2 by ring] at hadd
    have h1_pos : 1 + H / u ≠ 0 := by
      have : 0 ≤ H / u := div_nonneg hH hu_pos.le; linarith
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + H / t)) ((-H / u ^ 2) / (1 + H / u)) u :=
      h1.log h1_pos
    have h3 : HasDerivAt (fun t : ℝ => t * Real.log (1 + H / t))
        (1 * Real.log (1 + H / u) + u * ((-H / u ^ 2) / (1 + H / u))) u :=
      (hasDerivAt_id' u).mul h2
    have huH : u + H ≠ 0 := by linarith
    rwa [show 1 * Real.log (1 + H / u) + u * ((-H / u ^ 2) / (1 + H / u)) =
        Real.log (1 + H / u) - H / (u + H) by field_simp [hu_pos.ne', huH]; ring] at h3
  have hderiv_nn : ∀ u ∈ Set.Icc u₁ u₂, 0 ≤ Real.log (1 + H / u) - H / (u + H) := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le hu1 hu.1
    have huH_pos : 0 < u + H := by linarith
    have hlog_ge : H / (u + H) ≤ Real.log (1 + H / u) := by
      have h1 : 1 - (1 + H / u)⁻¹ ≤ Real.log (1 + H / u) := by
        have hx : 0 < (1 + H / u)⁻¹ := inv_pos.mpr (by positivity)
        have h := Real.log_le_sub_one_of_pos hx
        rw [Real.log_inv] at h
        linarith
      have heq : 1 - (1 + H / u)⁻¹ = H / (u + H) := by
        field_simp [hu_pos.ne', huH_pos.ne']
        ring
      rwa [heq] at h1
    linarith
  exact monotoneOn_of_deriv_nonneg (convex_Icc u₁ u₂)
    (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hderiv u (interior_subset hu)).deriv]
      exact hderiv_nn u (interior_subset hu))
    (Set.left_mem_Icc.mpr hu12) (Set.right_mem_Icc.mpr hu12) hu12

/-- **Slope-Window Collapse** (`CorFinal` in `SlopeExcessBoundExponentZero.lean`):
When `del ≤ 1/7`, `HH ≤ x^c * b`, `uF ≤ U`, and the combined frame defects satisfy
`(η + 4 * √e) * HH ≤ 6 * b`, `BostSlopeFiber.SlopeIneq` collapses directly into the linear
slope ceiling:
`B.s ≤ B.muCC + log |W| + 5 * (c + 1) * log x * (U + b) + 7 * b`. -/
theorem bost_slope_window_collapse (B : RHDirect.BostSlopeFiber) (U b x c : ℝ)
    (hx : 2 ≤ x) (hc : 0 ≤ c) (hb : 0 < b) (huF : 0 < B.uF) (hU : B.uF ≤ U)
    (hdel0 : 0 ≤ B.del) (hdel7 : B.del ≤ 1 / 7)
    (hη0 : 0 ≤ B.η) (he0 : 0 ≤ B.e) (he4 : B.e ≤ 1 / 4)
    (hHH_ge : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hHH_le : B.HH ≤ x ^ c * b)
    (hErr : (B.η + 4 * Real.sqrt B.e) * B.HH ≤ 6 * b)
    (hSlope : B.SlopeIneq) :
    B.s ≤ B.muCC + Real.log (B.cardW : ℝ) +
      5 * (c + 1) * Real.log x * (U + b) + 7 * b := by
  have hineq := hSlope hdel0 (by linarith) hη0 he0 he4 hHH_ge hHH_pos
  have h1m : (6 : ℝ) / 7 ≤ 1 - B.del := by linarith
  have hinv_le : (1 - B.del)⁻¹ ≤ 7 / 6 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 6 / 7) h1m
    norm_num at this; exact this
  have hinv_4 : (1 - B.del)⁻¹ * 4 ≤ 5 := by linarith
  have hinv_6 : (1 - B.del)⁻¹ * 6 ≤ 7 := by linarith
  have hphi_le : phi B.HH B.uF ≤ (U + b) * ((c + 1) * Real.log x) := by
    have hUpos : 0 < U + b := by linarith
    have hm := phi_mono hHH_pos.le huF (by linarith : B.uF ≤ U + b)
    unfold phi at hm ⊢
    have hxpos : 0 < x := by linarith
    have hxc1 : 1 ≤ x ^ c := Real.one_le_rpow (by linarith) hc
    have hdiv : B.HH / (U + b) ≤ x ^ c := by
      rw [div_le_iff₀ hUpos]
      calc B.HH ≤ x ^ c * b := hHH_le
        _ ≤ x ^ c * (U + b) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hlog : Real.log (1 + B.HH / (U + b)) ≤ (c + 1) * Real.log x := by
      have h1 : 1 + B.HH / (U + b) ≤ 2 * x ^ c := by linarith
      have h2 : 2 * x ^ c ≤ x * x ^ c := mul_le_mul_of_nonneg_right hx (by positivity)
      calc Real.log (1 + B.HH / (U + b))
          ≤ Real.log (x * x ^ c) := Real.log_le_log (by positivity) (le_trans h1 h2)
        _ = Real.log x + c * Real.log x := by
            rw [Real.log_mul hxpos.ne' (by positivity), Real.log_rpow hxpos]
        _ = (c + 1) * Real.log x := by ring
    exact le_trans hm (mul_le_mul_of_nonneg_left hlog hUpos.le)
  have hphi_nn : 0 ≤ phi B.HH B.uF := by
    unfold phi
    exact mul_nonneg huF.le (Real.log_nonneg (by linarith [div_nonneg hHH_pos.le huF.le]))
  have h1 : (1 - B.del)⁻¹ * (4 * phi B.HH B.uF) ≤ 5 * (c + 1) * Real.log x * (U + b) := by
    calc (1 - B.del)⁻¹ * (4 * phi B.HH B.uF)
        = ((1 - B.del)⁻¹ * 4) * phi B.HH B.uF := by ring
      _ ≤ 5 * phi B.HH B.uF := mul_le_mul_of_nonneg_right hinv_4 hphi_nn
      _ ≤ 5 * ((U + b) * ((c + 1) * Real.log x)) := mul_le_mul_of_nonneg_left hphi_le (by norm_num)
      _ = 5 * (c + 1) * Real.log x * (U + b) := by ring
  have h2 : (1 - B.del)⁻¹ * ((B.η + 4 * Real.sqrt B.e) * B.HH) ≤ 7 * b := by
    have hinv_nn : 0 ≤ (1 - B.del)⁻¹ := inv_nonneg.mpr (by linarith)
    calc (1 - B.del)⁻¹ * ((B.η + 4 * Real.sqrt B.e) * B.HH)
        ≤ (1 - B.del)⁻¹ * (6 * b) := mul_le_mul_of_nonneg_left hErr hinv_nn
      _ = ((1 - B.del)⁻¹ * 6) * b := by ring
      _ ≤ 7 * b := mul_le_mul_of_nonneg_right hinv_6 hb.le
  have hsplit : (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) =
      (1 - B.del)⁻¹ * (4 * phi B.HH B.uF) +
        (1 - B.del)⁻¹ * ((B.η + 4 * Real.sqrt B.e) * B.HH) := by
    unfold phi; ring
  linarith

end CorankShareAndLayerCake

end RHDirect.LatticeFrame

end
