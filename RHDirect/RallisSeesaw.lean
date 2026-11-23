import RHDirect.Interfaces
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# RHDirect.RallisSeesaw

Compact, self-contained, 0-`sorry`, 0-`axiom` formalization of the algebraic and inner-product
core of the Rallis seesaw, dual-pair adjointness, unitary spectral swaps, finite-field Gauss
operators, and the iterated column-chain operator `chainOpM` on rank-stepped unitary spaces
`X_j` of dimension `R.chainRank j = R.k + j * (R.t + 1)`.

## Structure

1. **Weighted Genus Inner Product & Abstract Seesaw Dual-Pair Adjointness (`wip`, `kerOp`, `kerAdj`)**:
   - Discrete genus/class-set seesaw identity `wip w' (kerOp w K f) g = wip w f (kerOp w' (kerAdj K) g)`.
   - Kernel composition `kerOp_comp` and adjoint involution / anti-multiplicativity.
   - Positivity, anisotropy (`wip_self_eq_zero_iff`), and seesaw Gram-kernel non-negativity
     (`kerOp_normSq_eq_seesaw`, `seesaw_gram_re_nonneg`).
2. **Hilbert-Space Seesaw Dual Pairs & Rallis Inner-Product Positivity**:
   - `SeesawDualPair` (`⟨θ(f), g⟩_H = ⟨f, θ*(g)⟩_G`), uniqueness of the seesaw adjoint,
     non-negativity `0 ≤ Re ⟨f, θ*(θ(f))⟩_G`, and the Rallis nonvanishing criterion
     `θ(f) ≠ 0 ↔ ⟨f, θ*(θ(f))⟩_G ≠ 0`.
   - Deduction of the scalar Rallis adjoint identity `θ*(θ(x)) = α • x` (`rallis_adjoint_of_hyp`),
     exact norm-square scaling `‖θ(x)‖^2 = Re(α) * ‖x‖^2`, positivity of the Rallis L-factor
     (`rallis_factor_nonneg_of_nonzero`), and the Petersson norm-ratio identity
     (`rallis_norm_ratio_identity`).
3. **Unitary Spectral Swaps, Quotient Rank, Block Determinants & Finite-Field Gauss Operators**:
   - `eigen_swap_finrank`, `rows_quot_of_injective_comp_adjoint`, `det_swap_orth`.
   - `det_blocks_of_isInternal` and `det_chain_factorization` for block-diagonal Rallis operators.
   - `gaussOp`, `gaussOpDual`, ramified inversion `gaussOp_comp_dual_on_ramified`, and
     unitary adjointness `gaussOp_adjoint`.
4. **Rank-Stepped Unitary Spaces `X_j` & Iterated Column-Chain Operator (`kerOpM`, `chainOpM`, `ColumnChainData`)**:
   - Arithmetic of `R.chainRank j = R.k + j * (R.t + 1)` (`chainRank_succ`, `chainRank_even`,
     `chainRank_step_half_diff`, `chainRank_strictMono`).
   - Linear iterated column-chain operator `chainOpM`, splitting `chainOpM_add`, denominator
     clearing / lattice integrality (`chainOpM_int_clearing`, `chainOpM_const_denom_clearing`),
     and `ColumnChainData` (rebuilding `DataKernels.ColumnChain.col := chainOpM C.wt C.Kmap R.m`
     together with `wt_pos`, `wt_eq_one_of_subsingleton`, `DGam_mul_wt_int`, `col_succ`).
5. **Exact Algebraic Norm & Stability Recursion Along `j = 0, ..., m`**:
   - Adjoint downward tower `downChain`, submodule stability `downChain_adjoint_mem`,
     exact scalar product recursion `chain_rallis_scalar_recursion`, multiplicative norm-square
     recursion `chain_normSq_recursion`, additive log-norm / slope decomposition
     `chain_log_normSq_additive`, inductive definite-chain nonvanishing
     `definite_chain_nonvanishing`, and operator-norm recursion for `chainOpM`
     (`chainOpM_norm_le`).
-/

open Finset RHDirect
open scoped BigOperators InnerProductSpace

namespace RHDirect.RallisSeesaw

noncomputable section

/-! ## Section 1: Weighted Genus Inner Products, Kernel Operators & Discrete Seesaw Adjointness -/

section DiscreteSeesaw

/-- Weighted Hermitian inner product `⟨f, g⟩_w = ∑ i, w i * star (f i) * g i` on a finite
genus / double-coset space `ι`. -/
def wip {R ι : Type*} [CommSemiring R] [StarRing R] [Fintype ι]
    (w : ι → R) (f g : ι → R) : R :=
  ∑ i, w i * star (f i) * g i

/-- Finite weighted integral-kernel operator `(K_w f)(j) = ∑ i, w i * f i * K i j`. -/
def kerOp {R ι κ : Type*} [CommSemiring R] [Fintype ι]
    (w : ι → R) (K : ι → κ → R) (f : ι → R) : κ → R :=
  fun j => ∑ i, w i * f i * K i j

/-- Adjoint (conjugate-transpose) kernel `K^*(j, i) = star (K i j)`. -/
def kerAdj {R ι κ : Type*} [Star R] (K : ι → κ → R) : κ → ι → R :=
  fun j i => star (K i j)

/-- Weighted composition of two finite kernels `(K₁ *_{w} K₂)(i, k) = ∑ j, K₁ i j * w j * K₂ j k`. -/
def kerMul {R ι κ μ : Type*} [CommSemiring R] [Fintype κ]
    (w : κ → R) (K₁ : ι → κ → R) (K₂ : κ → μ → R) : ι → μ → R :=
  fun i k => ∑ j, K₁ i j * w j * K₂ j k

/-- Double adjoint of a kernel is the original kernel. -/
theorem kerAdj_involutive {R ι κ : Type*} [InvolutiveStar R] (K : ι → κ → R) :
    kerAdj (kerAdj K) = K := by
  funext i j
  exact star_star (K i j)

/-- **Discrete Seesaw / Dual-Pair Adjointness Identity**:
for self-adjoint weights `w`, `⟨K_w(f), g⟩_{w'} = ⟨f, (K^*)_{w'}(g)⟩_w`. -/
theorem kerOp_adjoint {R ι κ : Type*} [CommSemiring R] [StarRing R] [Fintype ι] [Fintype κ]
    (w : ι → R) (w' : κ → R) (K : ι → κ → R) (f : ι → R) (g : κ → R)
    (hw : ∀ i, star (w i) = w i) :
    wip w' (kerOp w K f) g = wip w f (kerOp w' (kerAdj K) g) := by
  unfold wip kerOp kerAdj
  simp only [star_sum, star_mul, hw, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Composition of two weighted kernel operators equals the operator of the composed kernel. -/
theorem kerOp_comp {R ι κ μ : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    (w₁ : ι → R) (w₂ : κ → R) (K₁ : ι → κ → R) (K₂ : κ → μ → R) (f : ι → R) :
    kerOp w₂ K₂ (kerOp w₁ K₁ f) = kerOp w₁ (kerMul w₂ K₁ K₂) f := by
  funext k
  unfold kerOp kerMul
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Adjoint of a composed kernel reverses order when intermediate weights are self-adjoint. -/
theorem kerAdj_kerMul {R ι κ μ : Type*} [CommSemiring R] [StarRing R] [Fintype κ]
    (w : κ → R) (K₁ : ι → κ → R) (K₂ : κ → μ → R) (hw : ∀ j, star (w j) = w j) :
    kerAdj (kerMul w K₁ K₂) = kerMul w (kerAdj K₂) (kerAdj K₁) := by
  funext k i
  unfold kerAdj kerMul
  simp only [star_sum, star_mul, hw]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Seesaw Gram-Kernel Identity**:
`⟨K_w(f), K_w(f)⟩_{w'} = ⟨f, (K *_{w'} K^*)_w(f)⟩_w`. -/
theorem kerOp_normSq_eq_seesaw {R ι κ : Type*} [CommSemiring R] [StarRing R]
    [Fintype ι] [Fintype κ] (w : ι → R) (w' : κ → R) (K : ι → κ → R) (f : ι → R)
    (hw : ∀ i, star (w i) = w i) :
    wip w' (kerOp w K f) (kerOp w K f) =
      wip w f (kerOp w (kerMul w' K (kerAdj K)) f) := by
  rw [kerOp_adjoint w w' K f (kerOp w K f) hw, kerOp_comp]

/-- Complex weighted self-pairing equals the real sum `∑ i, w i * ‖f i‖ ^ 2`. -/
theorem wip_self_eq_sum_normSq {ι : Type*} [Fintype ι] (w : ι → ℝ) (f : ι → ℂ) :
    wip (fun i => (w i : ℂ)) f f = ((∑ i, w i * ‖f i‖ ^ 2 : ℝ) : ℂ) := by
  unfold wip
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, Complex.star_def, Complex.conj_mul']

/-- Non-negativity and reality of the weighted Hermitian form `wip` for non-negative real weights. -/
theorem wip_self_re_nonneg {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℂ) :
    0 ≤ (wip (fun i => (w i : ℂ)) f f).re ∧ (wip (fun i => (w i : ℂ)) f f).im = 0 := by
  rw [wip_self_eq_sum_normSq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _), rfl⟩

/-- Positive definiteness (anisotropy) of the weighted genus inner product when all weights are
strictly positive. -/
theorem wip_self_eq_zero_iff {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i) (f : ι → ℂ) :
    wip (fun i => (w i : ℂ)) f f = 0 ↔ f = 0 := by
  rw [wip_self_eq_sum_normSq, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _)]
  constructor
  · intro h
    funext i
    have hi := h i (Finset.mem_univ i)
    have hnorm : ‖f i‖ ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left (hw i).ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro h i _
    simp [h]

/-- **Discrete Rallis Seesaw Positivity**: for real weights `wG` and non-negative real weights `wH`,
the seesaw Gram pairing `⟨f, (K *_{wH} K^*)_{wG} f⟩_{wG}` is real and non-negative, and vanishes
(when `wH > 0`) if and only if the lift `kerOp wG K f` vanishes. -/
theorem seesaw_gram_re_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (wG : ι → ℝ) {wH : κ → ℝ} (hwH : ∀ j, 0 ≤ wH j) (K : ι → κ → ℂ) (f : ι → ℂ) :
    0 ≤ (wip (fun i => (wG i : ℂ)) f
          (kerOp (fun i => (wG i : ℂ)) (kerMul (fun j => (wH j : ℂ)) K (kerAdj K)) f)).re ∧
    (wip (fun i => (wG i : ℂ)) f
          (kerOp (fun i => (wG i : ℂ)) (kerMul (fun j => (wH j : ℂ)) K (kerAdj K)) f)).im = 0 := by
  have hwG : ∀ i, star (wG i : ℂ) = (wG i : ℂ) := fun i => Complex.conj_ofReal _
  rw [← kerOp_normSq_eq_seesaw _ _ K f hwG]
  exact wip_self_re_nonneg hwH _

theorem seesaw_gram_eq_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (wG : ι → ℝ) {wH : κ → ℝ} (hwH : ∀ j, 0 < wH j) (K : ι → κ → ℂ) (f : ι → ℂ) :
    wip (fun i => (wG i : ℂ)) f
      (kerOp (fun i => (wG i : ℂ)) (kerMul (fun j => (wH j : ℂ)) K (kerAdj K)) f) = 0 ↔
      kerOp (fun i => (wG i : ℂ)) K f = 0 := by
  have hwG : ∀ i, star (wG i : ℂ) = (wG i : ℂ) := fun i => Complex.conj_ofReal _
  rw [← kerOp_normSq_eq_seesaw _ _ K f hwG]
  exact wip_self_eq_zero_iff hwH _

end DiscreteSeesaw

/-! ## Section 2: Abstract Hilbert-Space Seesaw Dual Pairs & Rallis Inner-Product Positivity -/

section HilbertSeesaw

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- An abstract seesaw dual-pair correspondence `(θ, θ*)` between inner-product spaces `E` and `F`
satisfying the seesaw adjointness identity `⟨θ(f), g⟩_F = ⟨f, θ*(g)⟩_E`. -/
structure SeesawDualPair (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] where
  θ : E →ₗ[𝕜] F
  θAdj : F →ₗ[𝕜] E
  adjoint_eq : ∀ (x : E) (y : F), inner 𝕜 (θ x) y = inner 𝕜 x (θAdj y)

/-- In finite dimensions, every linear theta-lift map `θ : E →ₗ[𝕜] F` canonically defines a
`SeesawDualPair` via its Hilbert adjoint `LinearMap.adjoint θ`. -/
def SeesawDualPair.ofLinear [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (θ : E →ₗ[𝕜] F) : SeesawDualPair 𝕜 E F where
  θ := θ
  θAdj := LinearMap.adjoint θ
  adjoint_eq x y := (LinearMap.adjoint_inner_right θ x y).symm

/-- Uniqueness of the seesaw adjoint in finite dimensions: `P.θAdj = LinearMap.adjoint P.θ`. -/
theorem SeesawDualPair.θAdj_eq_adjoint [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (P : SeesawDualPair 𝕜 E F) :
    P.θAdj = LinearMap.adjoint P.θ := by
  ext y
  refine ext_inner_left 𝕜 fun x => ?_
  rw [← P.adjoint_eq x y, LinearMap.adjoint_inner_right]

/-- **Rallis Seesaw Norm Identity**: `⟨x, θ*(θ(x))⟩_E = ‖θ(x)‖^2`. -/
theorem SeesawDualPair.rallis_pairing_eq_normSq (P : SeesawDualPair 𝕜 E F) (x : E) :
    inner 𝕜 x (P.θAdj (P.θ x)) = ((‖P.θ x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← P.adjoint_eq, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Rallis Seesaw Non-Negativity**: `⟨x, θ*(θ(x))⟩_E` has non-negative real part and zero
imaginary part. -/
theorem SeesawDualPair.rallis_pairing_re_nonneg (P : SeesawDualPair 𝕜 E F) (x : E) :
    0 ≤ RCLike.re (inner 𝕜 x (P.θAdj (P.θ x))) ∧ RCLike.im (inner 𝕜 x (P.θAdj (P.θ x))) = 0 := by
  rw [P.rallis_pairing_eq_normSq x, RCLike.ofReal_re, RCLike.ofReal_im]
  exact ⟨sq_nonneg _, rfl⟩

/-- **Rallis Nonvanishing Criterion**: the theta lift `θ(x)` is nonzero if and only if the Rallis
inner product `⟨x, θ*(θ(x))⟩_E` is nonzero. -/
theorem SeesawDualPair.lift_ne_zero_iff (P : SeesawDualPair 𝕜 E F) (x : E) :
    P.θ x ≠ 0 ↔ inner 𝕜 x (P.θAdj (P.θ x)) ≠ 0 := by
  simp only [P.rallis_pairing_eq_normSq x, ne_eq, RCLike.ofReal_eq_zero, sq_eq_zero_iff,
    norm_eq_zero]

/-- Abstract Rallis inner-product formula on a submodule `S ≤ E`:
`⟨θ(x), θ(y)⟩_F = (c * L * ∏ v ∈ Pset, Z v) * ⟨x, y⟩_E` for all `x, y ∈ S`. -/
def RallisInnerProductHyp {P : Type*} (θ : E →ₗ[𝕜] F) (S : Submodule 𝕜 E)
    (Pset : Finset P) (c L : 𝕜) (Z : P → 𝕜) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, inner 𝕜 (θ x) (θ y) = c * L * (∏ v ∈ Pset, Z v) * inner 𝕜 x y

/-- **Rallis Adjoint Eigenvalue Identity (`RallisAdj`)**:
if `θ` satisfies `RallisInnerProductHyp` on a `θ* ∘ θ`-stable submodule `S ≤ E`, then `θ* ∘ θ`
acts on `S` as multiplication by the Rallis scalar `α = c * L * ∏ v ∈ Pset, Z v`. -/
theorem rallis_adjoint_of_hyp [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {P : Type*} (θ : E →ₗ[𝕜] F) (S : Submodule 𝕜 E) (Pset : Finset P) (c L : 𝕜) (Z : P → 𝕜)
    (hR : RallisInnerProductHyp θ S Pset c L Z)
    (hS : ∀ x ∈ S, LinearMap.adjoint θ (θ x) ∈ S) :
    ∀ x ∈ S, LinearMap.adjoint θ (θ x) = (c * L * ∏ v ∈ Pset, Z v) • x := by
  intro x hx
  set α : 𝕜 := c * L * ∏ v ∈ Pset, Z v
  have hmem : LinearMap.adjoint θ (θ x) - α • x ∈ S :=
    S.sub_mem (hS x hx) (S.smul_mem α hx)
  have hzero : inner 𝕜 (LinearMap.adjoint θ (θ x) - α • x)
      (LinearMap.adjoint θ (θ x) - α • x) = 0 := by
    have horth : ∀ y ∈ S, inner 𝕜 y (LinearMap.adjoint θ (θ x) - α • x) = 0 := by
      intro y hy
      rw [inner_sub_right, LinearMap.adjoint_inner_right, inner_smul_right, hR y hy x hx, sub_self]
    exact horth _ hmem
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- Exact norm-square scaling under the Rallis inner-product formula. -/
theorem rallis_normSq_scaling {P : Type*} {θ : E →ₗ[𝕜] F} {S : Submodule 𝕜 E}
    {Pset : Finset P} {c L : 𝕜} {Z : P → 𝕜}
    (hR : RallisInnerProductHyp θ S Pset c L Z) {x : E} (hx : x ∈ S) :
    ‖θ x‖ ^ 2 = RCLike.re (c * L * ∏ v ∈ Pset, Z v) * ‖x‖ ^ 2 := by
  have h := congrArg RCLike.re (hR x hx x hx)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hL : RCLike.re (((‖θ x‖ : 𝕜) ^ 2)) = ‖θ x‖ ^ 2 := by
    rw [show ((‖θ x‖ : 𝕜) ^ 2) = ((‖θ x‖ ^ 2 : ℝ) : 𝕜) by norm_cast, RCLike.ofReal_re]
  have hR' : RCLike.re ((c * L * ∏ v ∈ Pset, Z v) * ((‖x‖ : 𝕜) ^ 2)) =
      RCLike.re (c * L * ∏ v ∈ Pset, Z v) * ‖x‖ ^ 2 := by
    rw [show ((‖x‖ : 𝕜) ^ 2) = ((‖x‖ ^ 2 : ℝ) : 𝕜) by norm_cast, RCLike.mul_re,
      RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  rw [hL, hR'] at h
  exact h

/-- **Positivity of the Rallis L-Factor**: whenever `S` contains a nonzero vector `x`, the Rallis
scalar `α = c * L * ∏ v ∈ Pset, Z v` is real and non-negative (`0 ≤ Re α`, `Im α = 0`). -/
theorem rallis_factor_nonneg_of_nonzero {P : Type*} {θ : E →ₗ[𝕜] F} {S : Submodule 𝕜 E}
    {Pset : Finset P} {c L : 𝕜} {Z : P → 𝕜}
    (hR : RallisInnerProductHyp θ S Pset c L Z) {x : E} (hx : x ∈ S) (hx0 : x ≠ 0) :
    0 ≤ RCLike.re (c * L * ∏ v ∈ Pset, Z v) ∧ RCLike.im (c * L * ∏ v ∈ Pset, Z v) = 0 := by
  have hnorm_pos : (0 : ℝ) < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hscale := rallis_normSq_scaling hR hx
  have hre : 0 ≤ RCLike.re (c * L * ∏ v ∈ Pset, Z v) := by
    by_contra hneg
    push Not at hneg
    have : ‖θ x‖ ^ 2 < 0 := by
      rw [hscale]
      exact mul_neg_of_neg_of_pos hneg hnorm_pos
    linarith [sq_nonneg ‖θ x‖]
  have him : RCLike.im (c * L * ∏ v ∈ Pset, Z v) = 0 := by
    have h := congrArg RCLike.im (hR x hx x hx)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    rw [show ((‖θ x‖ : 𝕜) ^ 2) = ((‖θ x‖ ^ 2 : ℝ) : 𝕜) by norm_cast,
      show ((‖x‖ : 𝕜) ^ 2) = ((‖x‖ ^ 2 : ℝ) : 𝕜) by norm_cast,
      RCLike.ofReal_im, RCLike.mul_im, RCLike.ofReal_re, RCLike.ofReal_im,
      mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hnorm_pos.ne'
  exact ⟨hre, him⟩

/-- If `x ∈ S` is nonzero and the Rallis scalar `α ≠ 0`, then the theta lift `θ x` is nonzero. -/
theorem rallis_lift_ne_zero_of_factor_ne_zero {P : Type*} {θ : E →ₗ[𝕜] F} {S : Submodule 𝕜 E}
    {Pset : Finset P} {c L : 𝕜} {Z : P → 𝕜}
    (hR : RallisInnerProductHyp θ S Pset c L Z) {x : E} (hx : x ∈ S) (hx0 : x ≠ 0)
    (hα : c * L * ∏ v ∈ Pset, Z v ≠ 0) :
    θ x ≠ 0 := by
  intro hz
  have h := hR x hx x hx
  rw [hz, inner_zero_left] at h
  have hinner_ne : inner 𝕜 x x ≠ 0 := by
    rwa [ne_eq, inner_self_eq_zero]
  exact mul_ne_zero hα hinner_ne h.symm

/-- **Petersson Norm-Ratio Identity** (matching `big_theta_petersson_norm_ratio_eq`):
if two theta lifts have Petersson norms `N₁ = c * L₁` and `N₂ = c * L₂` sharing the same
geometric/archimedean factor `c`, then `N₁ * L₂ = N₂ * L₁`. -/
theorem rallis_norm_ratio_identity {R : Type*} [CommRing R] {N₁ N₂ c L₁ L₂ : R}
    (h₁ : N₁ = c * L₁) (h₂ : N₂ = c * L₂) :
    N₁ * L₂ = N₂ * L₁ := by
  rw [h₁, h₂]
  ring

end HilbertSeesaw

/-! ## Section 3: Unitary Spectral Swaps, Quotient Rank, Block Determinants & Gauss Operators -/

section SpectralAndGauss

private theorem eigen_swap_finrank_le {𝕜 U V : Type*} [Field 𝕜]
    [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (P : U →ₗ[𝕜] V) (Q : V →ₗ[𝕜] U) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (Q ∘ₗ P) μ) ≤
      Module.finrank 𝕜 (Module.End.eigenspace (P ∘ₗ Q) μ) := by
  have hmap : ∀ x ∈ Module.End.eigenspace (Q ∘ₗ P) μ,
      P x ∈ Module.End.eigenspace (P ∘ₗ Q) μ := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    simp only [LinearMap.comp_apply] at hx ⊢
    rw [hx, map_smul]
  refine LinearMap.finrank_le_finrank_of_injective (f := P.restrict hmap) ?_
  intro x y hxy
  have hx := Module.End.mem_eigenspace_iff.mp x.2
  have hy := Module.End.mem_eigenspace_iff.mp y.2
  have hP : P x = P y := congrArg Subtype.val hxy
  apply Subtype.ext
  have hsmul : μ • (x : U) = μ • (y : U) := by
    rw [← hx, ← hy]
    simp [hP]
  exact smul_right_injective U hμ hsmul

/-- **Eigenvalue Multiplicity Swap (`EigenSwap`)**: for any linear maps `A : E →ₗ[𝕜] F`,
`B : F →ₗ[𝕜] E` and nonzero `μ ≠ 0`, `B ∘ A` and `A ∘ B` have equal `μ`-eigenspace dimensions. -/
theorem eigen_swap_finrank {𝕜 E F : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (B ∘ₗ A) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘ₗ B) μ) :=
  le_antisymm (eigen_swap_finrank_le A B hμ) (eigen_swap_finrank_le B A hμ)

/-- **Rows-Quotient Exactness (`RowsQuot`)**: if `ι ∘ ι*` is injective, then `ι` is surjective,
`(ker ι)ᗮ = range (ι*)`, and `finrank (E ⧸ ker ι) = finrank F`. -/
theorem rows_quot_of_injective_comp_adjoint {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (ι : E →ₗ[𝕜] F) (hinj : Function.Injective (ι ∘ₗ LinearMap.adjoint ι)) :
    LinearMap.range ι = ⊤ ∧
    (LinearMap.ker ι)ᗮ = LinearMap.range (LinearMap.adjoint ι) ∧
    Module.finrank 𝕜 (E ⧸ LinearMap.ker ι) = Module.finrank 𝕜 F := by
  have hsurj_comp : Function.Surjective (ι ∘ₗ LinearMap.adjoint ι) :=
    (LinearMap.injective_iff_surjective (f := ι ∘ₗ LinearMap.adjoint ι)).mp hinj
  have hrange : LinearMap.range ι = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨z, hz⟩ := hsurj_comp y
    exact ⟨LinearMap.adjoint ι z, hz⟩
  have hker_adj : LinearMap.ker (LinearMap.adjoint ι) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply hinj
    simp [hy]
  have horth_le : LinearMap.range (LinearMap.adjoint ι) ≤ (LinearMap.ker ι)ᗮ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hx, inner_zero_left]
  have hrank_orth : Module.finrank 𝕜 (LinearMap.ker ι)ᗮ =
      Module.finrank 𝕜 (LinearMap.range (LinearMap.adjoint ι)) := by
    have h1 := (LinearMap.ker ι).finrank_add_finrank_orthogonal
    have h2 := LinearMap.finrank_range_add_finrank_ker ι
    rw [LinearMap.finrank_range_adjoint]
    omega
  have horth : (LinearMap.ker ι)ᗮ = LinearMap.range (LinearMap.adjoint ι) :=
    (Submodule.eq_of_le_of_finrank_eq horth_le hrank_orth.symm).symm
  have hquot : Module.finrank 𝕜 (E ⧸ LinearMap.ker ι) = Module.finrank 𝕜 F := by
    have h := LinearMap.finrank_range_add_finrank_ker ι
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.ker ι)
    rw [hrange, finrank_top] at h
    omega
  exact ⟨hrange, horth, hquot⟩

/-- **Orthogonal Determinant Swap (`DetSwap`)**: the restrictions of `T* ∘ T` to `(ker T)ᗮ` and
of `T ∘ T*` to `(ker T*)ᗮ` have the exact same determinant. -/
theorem det_swap_orth {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F)
    (h₁ : ∀ x ∈ (LinearMap.ker T)ᗮ, (LinearMap.adjoint T ∘ₗ T) x ∈ (LinearMap.ker T)ᗮ)
    (h₂ : ∀ y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ,
      (T ∘ₗ LinearMap.adjoint T) y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ) :
    LinearMap.det ((LinearMap.adjoint T ∘ₗ T).restrict h₁) =
      LinearMap.det ((T ∘ₗ LinearMap.adjoint T).restrict h₂) := by
  have hmem_orth : ∀ x : E, T x ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← LinearMap.adjoint_inner_left, LinearMap.mem_ker.mp hu, inner_zero_left]
  let restr : (LinearMap.ker T)ᗮ →ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
    (T.comp (LinearMap.ker T)ᗮ.subtype).codRestrict _ (fun x => hmem_orth x)
  have hinj : Function.Injective restr := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : T x = 0 := congrArg Subtype.val hx
    have hmem : (x : E) ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨h0, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hfin : Module.finrank 𝕜 (LinearMap.ker T)ᗮ =
      Module.finrank 𝕜 (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
    have h1 := (LinearMap.ker T).finrank_add_finrank_orthogonal
    have h2 := LinearMap.finrank_range_add_finrank_ker T
    have h3 := (LinearMap.ker (LinearMap.adjoint T)).finrank_add_finrank_orthogonal
    have h4 := LinearMap.finrank_range_add_finrank_ker (LinearMap.adjoint T)
    have h5 := LinearMap.finrank_range_adjoint T
    omega
  let e : (LinearMap.ker T)ᗮ ≃ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
    LinearEquiv.ofBijective restr
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  have he_val : ∀ z : (LinearMap.ker T)ᗮ, ((e z : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T z :=
    fun _ => rfl
  have hconj :
      (T ∘ₗ LinearMap.adjoint T).restrict h₂ =
        e.toLinearMap ∘ₗ ((LinearMap.adjoint T ∘ₗ T).restrict h₁ ∘ₗ e.symm.toLinearMap) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.restrict_apply]
    rw [he_val, he_val]
  rw [hconj, LinearMap.det_conj]

/-- **Block-Scalar Determinant Formula (`DetBlocks`)**: if `E` decomposes as an internal direct
sum `⨁ s, Es s` and `A` acts as scalar `c s` on `Es s`, then `det A = ∏ s, c s ^ finrank (Es s)`. -/
theorem det_blocks_of_isInternal {𝕜 E σ : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [Fintype σ] [DecidableEq σ] (Es : σ → Submodule 𝕜 E) (hInt : DirectSum.IsInternal Es)
    (A : E →ₗ[𝕜] E) (c : σ → 𝕜) (hA : ∀ s, ∀ x ∈ Es s, A x = c s • x) :
    LinearMap.det A = ∏ s, c s ^ Module.finrank 𝕜 (Es s) := by
  let b : ∀ s, Module.Basis (Fin (Module.finrank 𝕜 (Es s))) 𝕜 (Es s) :=
    fun s => Module.finBasis 𝕜 (Es s)
  let B : Module.Basis (Σ s, Fin (Module.finrank 𝕜 (Es s))) 𝕜 E :=
    hInt.collectedBasis b
  rw [← LinearMap.det_toMatrix B]
  have hmat : LinearMap.toMatrix B B A =
      Matrix.diagonal (fun p : Σ s, Fin (Module.finrank 𝕜 (Es s)) => c p.1) := by
    ext p q
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    have hBq : B q ∈ Es q.1 := by
      simp only [B, DirectSum.IsInternal.collectedBasis_coe]
      exact (b q.1 q.2).2
    rw [hA q.1 (B q) hBq, map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hmat, Matrix.det_diagonal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

/-- **Chain Determinant Factorization (`DetChain`)**: determinant of a product-scalar operator `A`
acting on `⨁ s, Es s` by `κ * ∏ j, lam j s` factors into `κ ^ finrank E * ∏ j, det (B j)`. -/
theorem det_chain_factorization {𝕜 E σ : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [Fintype σ] [DecidableEq σ] {m : ℕ} (W : Fin m → Type*)
    [∀ j, AddCommGroup (W j)] [∀ j, Module 𝕜 (W j)] [∀ j, FiniteDimensional 𝕜 (W j)]
    (Es : σ → Submodule 𝕜 E) (Ws : ∀ j, σ → Submodule 𝕜 (W j))
    (hE : DirectSum.IsInternal Es) (hW : ∀ j, DirectSum.IsInternal (Ws j))
    (hrank : ∀ j s, Module.finrank 𝕜 (Ws j s) = Module.finrank 𝕜 (Es s))
    (κ : 𝕜) (lam : Fin m → σ → 𝕜) (A : E →ₗ[𝕜] E) (B : ∀ j, W j →ₗ[𝕜] W j)
    (hA : ∀ s, ∀ x ∈ Es s, A x = (κ * ∏ j, lam j s) • x)
    (hB : ∀ j s, ∀ x ∈ Ws j s, B j x = lam j s • x) :
    LinearMap.det A = κ ^ Module.finrank 𝕜 E * ∏ j, LinearMap.det (B j) := by
  rw [det_blocks_of_isInternal Es hE A _ hA]
  have hBdet : ∀ j, LinearMap.det (B j) = ∏ s, lam j s ^ Module.finrank 𝕜 (Es s) := by
    intro j
    rw [det_blocks_of_isInternal (Ws j) (hW j) (B j) (lam j) (hB j)]
    exact Finset.prod_congr rfl fun s _ => by rw [hrank j s]
  simp_rw [hBdet]
  have hfinE : Module.finrank 𝕜 E = ∑ s, Module.finrank 𝕜 (Es s) := by
    let B' := hE.collectedBasis (fun s => Module.finBasis 𝕜 (Es s))
    rw [Module.finrank_eq_card_basis B', Fintype.card_sigma]
    simp
  have hpow : ∀ t : Finset σ, κ ^ ∑ s ∈ t, Module.finrank 𝕜 (Es s) =
      ∏ s ∈ t, κ ^ Module.finrank 𝕜 (Es s) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, pow_add, ih, Finset.prod_insert ha]
  rw [hfinE, hpow Finset.univ]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow]
  congr 1
  exact Finset.prod_comm

/-- Finite-field Gauss sum operator `G(ψ, ρ) = ∑ c : 𝔽ˣ, ψ(c) • ρ(c)` (matching `DataKernels`). -/
def gaussOp {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ c

/-- Dual finite-field Gauss sum operator `G*(ψ, ρ) = ∑ c : 𝔽ˣ, ψ(-c) • ρ(c⁻¹)`. -/
def gaussOpDual {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (-(c : 𝔽)) • ρ c⁻¹

private theorem sum_units_eq_sub_zero {𝔽 M : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x : 𝔽, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

private theorem sum_units_addChar {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub_zero (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]

private theorem gauss_sum_core {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [AddCommGroup V] [Module ℂ V] (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1)
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_addChar ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp

/-- **Ramified Gauss Operator Inversion (`FactGaussRam` / `GaussOp`)**:
on the ramified subspace `ker (∑ c : 𝔽ˣ, ρ c)`, `G(ψ, ρ) ∘ G*(ψ, ρ)` and `G*(ψ, ρ) ∘ G(ψ, ρ)`
both equal scalar multiplication by `|𝔽|`. -/
theorem gaussOp_comp_dual_on_ramified {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [AddCommGroup V] [Module ℂ V] (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V))
    (hψ : ψ ≠ 1) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    gaussOp ψ ρ (gaussOpDual ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v ∧
    gaussOpDual ψ ρ (gaussOp ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v := by
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · simp only [gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d)
        (fun e => ψ (-(d : 𝔽)) • ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun _ => rfl)]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun d _ => step d, Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact gauss_sum_core ψ hψ ρ v hv
  · simp only [gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c)
        (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun _ => rfl)]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun c _ => step c, Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact gauss_sum_core ψ hψ ρ v hv

/-- **Unitary Adjointness of the Gauss Operator (`GaussOpAdj`)**:
when `ρ : 𝔽ˣ →* End(V)` is unitary, `LinearMap.adjoint (gaussOp ψ ρ) = gaussOpDual ψ ρ`. -/
theorem gaussOp_adjoint {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V))
    (hunit : ∀ (c : 𝔽ˣ) (x y : V), inner ℂ (ρ c x) (ρ c y) = inner ℂ x y) :
    LinearMap.adjoint (gaussOp ψ ρ) = gaussOpDual ψ ρ := by
  have hψ_conj : ∀ a : 𝔽, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a
    have hpow : (ψ a) ^ Fintype.card 𝔽 = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have hnorm : ‖ψ a‖ = 1 := by
      have h1 : ‖ψ a‖ ^ Fintype.card 𝔽 = 1 := by rw [← norm_pow, hpow, norm_one]
      have hpos : 0 < Fintype.card 𝔽 := Fintype.card_pos
      rcases lt_trichotomy ‖ψ a‖ 1 with hlt | heq | hgt
      · exfalso
        have := pow_lt_one₀ (norm_nonneg _) hlt hpos.ne'
        linarith
      · exact heq
      · exfalso
        have := one_lt_pow₀ hgt hpos.ne'
        linarith
    have hmul : (starRingEnd ℂ) (ψ a) * ψ a = 1 := by
      rw [Complex.conj_mul', hnorm]
      norm_num
    have hinv : ψ (-a) * ψ a = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    have hne : ψ a ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hinv; exact zero_ne_one hinv
    exact mul_right_cancel₀ hne (hmul.trans hinv.symm)
  have hρ_adj : ∀ c : 𝔽ˣ, LinearMap.adjoint (ρ c) = ρ c⁻¹ := by
    intro c
    ext y
    refine ext_inner_left ℂ fun x => ?_
    rw [LinearMap.adjoint_inner_right, ← hunit c x (ρ c⁻¹ y)]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [LinearMap.adjoint_inner_right]
  simp only [gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hψ_conj, ← LinearMap.adjoint_inner_right, hρ_adj]

end SpectralAndGauss

/-! ## Section 4: Rank-Stepped Unitary Spaces `X_j` & Iterated Column-Chain Operator `chainOpM` -/

section ColumnChainOperator

/-- Base rank of the chain `X_0` is `R.k`. -/
theorem chainRank_zero (R : ChainRanks) : R.chainRank 0 = R.k := by
  simp [ChainRanks.chainRank]

/-- Each step `X_j → X_{j+1}` increases the unitary rank by `R.t + 1`. -/
theorem chainRank_succ (R : ChainRanks) (j : ℕ) :
    R.chainRank (j + 1) = R.chainRank j + (R.t + 1) := by
  simp only [ChainRanks.chainRank]
  ring

/-- Every space `X_j` in the chain has even rank when `R.k` is even and `R.t` is odd. -/
theorem chainRank_even (R : ChainRanks) (hk : Even R.k) (ht : Odd R.t) (j : ℕ) :
    Even (R.chainRank j) := by
  unfold ChainRanks.chainRank
  have ht1 : Even (R.t + 1) := ht.add_one
  exact hk.add (ht1.mul_left j)

/-- Half-rank shift between consecutive steps `X_j` and `X_{j+1}` equals `(t + 1) / 2`
(matching `FactSShift` and `FactSDivSharp` in `Params.lean` / `DataKernels.lean`). -/
theorem chainRank_step_half_diff (R : ChainRanks) (j : ℕ) :
    ((R.chainRank (j + 1) : ℚ) - (R.chainRank j : ℚ)) / 2 = ((R.t : ℚ) + 1) / 2 := by
  rw [chainRank_succ]
  push_cast
  ring

/-- The rank sequence `j ↦ R.chainRank j` is strictly increasing. -/
theorem chainRank_strictMono (R : ChainRanks) : StrictMono R.chainRank := by
  intro a b hab
  simp only [ChainRanks.chainRank]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hab (Nat.succ_pos R.t)) R.k

/-- Module-valued weighted kernel operator `(K_w f)(j) = ∑ i, w i • K i j (f i)`. -/
def kerOpM {R ι κ M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι]
    (w : ι → R) (K : ι → κ → (M →ₗ[R] N)) (f : ι → M) : κ → N :=
  fun j => ∑ i, w i • K i j (f i)

/-- `kerOpM` packaged as an `R`-linear map `(ι → M) →ₗ[R] (κ → N)`. -/
def kerOpMLinear {R ι κ M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι]
    (w : ι → R) (K : ι → κ → (M →ₗ[R] N)) : (ι → M) →ₗ[R] (κ → N) where
  toFun := kerOpM w K
  map_add' f g := by
    funext j
    simp only [kerOpM, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext j
    simp only [kerOpM, Pi.smul_apply, map_smul, smul_comm c, Finset.smul_sum, RingHom.id_apply]

/-- Iterated column-chain operator `chainOpM` composing `m` step kernels
`K 0, ..., K (m - 1)` with weights `w 0, ..., w (m - 1)` from stage `0` to stage `m`. -/
def chainOpM {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) :
    (m : ℕ) → (ι 0 → M 0) → (ι m → M m)
  | 0, f => f
  | m + 1, f => kerOpM (w m) (K m) (chainOpM w K m f)

/-- `chainOpM` packaged as an `R`-linear map `(ι 0 → M 0) →ₗ[R] (ι m → M m)`. -/
def chainOpMLinear {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) :
    (m : ℕ) → ((ι 0 → M 0) →ₗ[R] (ι m → M m))
  | 0 => LinearMap.id
  | m + 1 => (kerOpMLinear (w m) (K m)).comp (chainOpMLinear w K m)

@[simp]
theorem chainOpMLinear_apply {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1)))
    (m : ℕ) (f : ι 0 → M 0) :
    chainOpMLinear w K m f = chainOpM w K m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [chainOpMLinear, chainOpM, LinearMap.comp_apply, ih]
    rfl

@[simp]
theorem chainOpM_zero {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) (f : ι 0 → M 0) :
    chainOpM w K 0 f = f := rfl

@[simp]
theorem chainOpM_succ {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1)))
    (m : ℕ) (f : ι 0 → M 0) :
    chainOpM w K (m + 1) f = kerOpM (w m) (K m) (chainOpM w K m f) := rfl

/-- **Chain Splitting / Semigroup Property**: running `chainOpM` for `m₁ + m₂` steps equals
running `m₁` steps followed by the shifted `m₂`-step chain starting at stage `m₁`. -/
theorem chainOpM_add {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1)))
    (m₁ m₂ : ℕ) (f : ι 0 → M 0) :
    chainOpM w K (m₁ + m₂) f =
      chainOpM (ι := fun j => ι (m₁ + j)) (M := fun j => M (m₁ + j))
        (fun j => w (m₁ + j)) (fun j => K (m₁ + j)) m₂ (chainOpM w K m₁ f) := by
  induction m₂ with
  | zero => rfl
  | succ m₂ ih =>
    exact congrArg (kerOpM (w (m₁ + m₂)) (K (m₁ + m₂))) ih

/-- **Column-Chain Integrality & Denominator Clearing (`ChainIntM`)**:
if `D j * w j i ∈ S` clears the stabilizer denominators at step `j` and `K j a b` preserves
the integral lattices `Λ j → Λ (j + 1)`, then `(∏ j < m, D j) • chainOpM w K m f y ∈ Λ m`. -/
theorem chainOpM_int_clearing {R : Type*} [CommRing R] (S : Subring R)
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (Λ : ∀ j, AddSubgroup (M j))
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1)))
    (D : ℕ → R)
    (hS : ∀ j, ∀ s ∈ S, ∀ x ∈ Λ j, s • x ∈ Λ j)
    (hw : ∀ j i, D j * w j i ∈ S)
    (hK : ∀ j a b, ∀ x ∈ Λ j, K j a b x ∈ Λ (j + 1))
    (f : ι 0 → M 0) (hf : ∀ i, f i ∈ Λ 0) :
    ∀ (m : ℕ) (y : ι m), (∏ j ∈ Finset.range m, D j) • chainOpM w K m f y ∈ Λ m := by
  intro m
  induction m with
  | zero =>
    intro y
    simpa using hf y
  | succ m ih =>
    intro y
    rw [Finset.prod_range_succ, chainOpM_succ, kerOpM, Finset.smul_sum]
    refine AddSubgroup.sum_mem (Λ (m + 1)) fun a _ => ?_
    have hstep : ((∏ j ∈ Finset.range m, D j) * D m) • w m a • K m a y (chainOpM w K m f a) =
        (D m * w m a) • K m a y ((∏ j ∈ Finset.range m, D j) • chainOpM w K m f a) := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      ring
    rw [hstep]
    exact hS (m + 1) (D m * w m a) (hw m a) _ (hK m a y _ (ih a))

/-- Constant-denominator specialization: when a single genus denominator `DGam` clears all
stabilizer weights `w j i` up to step `m`, `DGam ^ m • chainOpM w K m f y ∈ Λ m`. -/
theorem chainOpM_const_denom_clearing {R : Type*} [CommRing R] (S : Subring R)
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (Λ : ∀ j, AddSubgroup (M j))
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1)))
    (DGam : R)
    (hS : ∀ j, ∀ s ∈ S, ∀ x ∈ Λ j, s • x ∈ Λ j)
    (hw : ∀ j i, DGam * w j i ∈ S)
    (hK : ∀ j a b, ∀ x ∈ Λ j, K j a b x ∈ Λ (j + 1))
    (f : ι 0 → M 0) (hf : ∀ i, f i ∈ Λ 0) (m : ℕ) (y : ι m) :
    DGam ^ m • chainOpM w K m f y ∈ Λ m := by
  simpa using chainOpM_int_clearing S Λ w K (fun _ => DGam) hS hw hK f hf m y

/-- Pointwise multiplication operator `(mulFun g φ)(y) = g y * φ y` (matching `DataKernels`). -/
def mulFun {Y : Type*} (g : Y → ℂ) : (Y → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := fun y => g y * φ y
  map_add' φ ψ := by funext y; simp [mul_add]
  map_smul' c φ := by funext y; simp; ring

/-- Clean, dead-field-free formalization of `DataKernels.ColumnChain` on rank-stepped unitary
spaces `X_j` of rank `R.chainRank j = R.k + j * (R.t + 1)`. -/
structure ColumnChainData (R : ChainRanks) (ι : Type) [Fintype ι] where
  cls : ℕ → Type
  [clsFin : ∀ j, Fintype (cls j)]
  stab : ∀ j, cls j → Type
  [stabGrp : ∀ j c, Group (stab j c)]
  [stabFin : ∀ j c, Finite (stab j c)]
  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd_DGam : ∀ j, j ≤ R.m → ∀ c, Nat.card (stab j c) ∣ DGam
  Y : ℕ → Type
  de : ∀ j, Y j → ι → ℂ
  de_ne : ∀ j y τ, de j y τ ≠ 0
  rhoDet : ∀ j, cls j → ℂ
  rhoDet' : ∀ j, cls (j + 1) → ℂ
  rho_norm : ∀ j, j < R.m → ∀ c, ‖rhoDet j c‖ = 1
  rho'_norm : ∀ j, j < R.m → ∀ c, ‖rhoDet' j c‖ = 1
  unf : ∀ j, cls j → cls (j + 1) → ((Y j → ℂ) →ₗ[ℂ] (Y (j + 1) → ℂ))
  sSharp : ℕ → ι → ℤ
  sDiv : ℕ → ι → ℤ

attribute [instance] ColumnChainData.clsFin ColumnChainData.stabGrp ColumnChainData.stabFin

namespace ColumnChainData

variable {R : ChainRanks} {ι : Type} [Fintype ι] (C : ColumnChainData R ι)

/-- Rank of the `j`-th unitary space `X_j` in the column chain. -/
def stageRank (_C : ColumnChainData R ι) (j : ℕ) : ℕ := R.chainRank j

/-- Genus stabilizer weight `w_j(c) = |stab_j(c)|⁻¹`. -/
def wt (j : ℕ) (c : C.cls j) : ℂ := ((Nat.card (C.stab j c) : ℕ) : ℂ)⁻¹

/-- Pre-step determinant-power scaling `sharp j`. -/
def sharp (j : ℕ) : (C.Y j → ℂ) →ₗ[ℂ] (C.Y j → ℂ) :=
  mulFun (fun y => ∏ τ, (C.de j y τ) ^ (C.sSharp j τ))

/-- Post-step determinant-power division `divDe j`. -/
def divDe (j : ℕ) : (C.Y (j + 1) → ℂ) →ₗ[ℂ] (C.Y (j + 1) → ℂ) :=
  mulFun (fun y' => (∏ τ, (C.de (j + 1) y' τ) ^ (C.sDiv j τ))⁻¹)

/-- Twisted step kernel `Kmap j L L'`. -/
def Kmap (j : ℕ) (L : C.cls j) (L' : C.cls (j + 1)) :
    (C.Y j → ℂ) →ₗ[ℂ] (C.Y (j + 1) → ℂ) :=
  (C.rhoDet j L * C.rhoDet' j L') • ((C.divDe j).comp ((C.unf j L L').comp (C.sharp j)))

/-- Single-step column operator `K j`. -/
def K (j : ℕ) (φ : C.cls j → C.Y j → ℂ) : C.cls (j + 1) → C.Y (j + 1) → ℂ :=
  kerOpM (C.wt j) (C.Kmap j) φ

/-- Full `m`-step iterated column operator `col := chainOpM C.wt C.Kmap R.m`
(exact counterpart of `DataKernels.ColumnChain.col`). -/
def col (φ : C.cls 0 → C.Y 0 → ℂ) : C.cls R.m → C.Y R.m → ℂ :=
  chainOpM C.wt C.Kmap R.m φ

/-- Stabilizer cardinality is always strictly positive (`FactWtPos`). -/
theorem card_stab_pos (j : ℕ) (c : C.cls j) : 0 < Nat.card (C.stab j c) :=
  Nat.card_pos

/-- At a neat/trivial-stabilizer base level, `C.wt 0 c = 1` (`FactWtZero`). -/
theorem wt_zero_eq_one (hsub : ∀ c, Subsingleton (C.stab 0 c)) (c : C.cls 0) :
    C.wt 0 c = 1 := by
  have : Unique (C.stab 0 c) := uniqueOfSubsingleton (1 : C.stab 0 c)
  simp [wt]

/-- `DGam` clears every stabilizer denominator along `j ≤ R.m` (`FactWtInt`). -/
theorem DGam_mul_wt_int {j : ℕ} (hj : j ≤ R.m) (c : C.cls j) :
    ∃ z : ℤ, (C.DGam : ℂ) * C.wt j c = z := by
  obtain ⟨q, hq⟩ := C.dvd_DGam j hj c
  refine ⟨(q : ℤ), ?_⟩
  have hpos : (Nat.card (C.stab j c) : ℂ) ≠ 0 := by
    exact_mod_cast (C.card_stab_pos j c).ne'
  rw [wt, hq]
  push_cast
  field_simp [hpos]

/-- Step-index bridge for `chainOpM` (`bridge_thl_index`). -/
theorem chainOpM_step_eq_K (φ : C.cls 0 → C.Y 0 → ℂ) (j : ℕ) :
    chainOpM C.wt C.Kmap (j + 1) φ = C.K j (chainOpM C.wt C.Kmap j φ) := rfl

/-- Unitary determinant phase factors have norm `1`. -/
theorem norm_rhoDet_mul_rhoDet' {j : ℕ} (hj : j < R.m) (L : C.cls j) (L' : C.cls (j + 1)) :
    ‖C.rhoDet j L * C.rhoDet' j L'‖ = 1 := by
  rw [norm_mul, C.rho_norm j hj L, C.rho'_norm j hj L', one_mul]

end ColumnChainData

end ColumnChainOperator

/-! ## Section 5: Exact Algebraic Norm & Stability Recursion Along `j = 0, ..., m` -/

section ChainNormAndStability

/-- Downward chain composition `T_0 ∘ T_1 ∘ ... ∘ T_{m-1} : E m →ₗ[𝕜] E 0` along rank-stepped
inner-product spaces `E 0, E 1, ..., E m`. -/
def downChain {𝕜 : Type*} [CommSemiring 𝕜] {E : ℕ → Type*}
    [∀ j, AddCommMonoid (E j)] [∀ j, Module 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) : (m : ℕ) → (E m →ₗ[𝕜] E 0)
  | 0 => LinearMap.id
  | m + 1 => (downChain T m).comp (T m)

/-- Adjoint of the downward chain iterates the upward seesaw lifts:
`(downChain T (m + 1))* = (T m)* ∘ (downChain T m)*`. -/
theorem downChain_adjoint_succ {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (m : ℕ) (x : E 0) :
    LinearMap.adjoint (downChain T (m + 1)) x =
      LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x) := by
  show LinearMap.adjoint ((downChain T m).comp (T m)) x = _
  rw [LinearMap.adjoint_comp]
  rfl

/-- **Stability Recursion Along `j = 0, ..., m`**:
if each upward lift `(T j)*` preserves the chosen automorphic/cuspidal submodules `S j → S (j+1)`,
then the `m`-step upward lift `(downChain T m)*` maps `S 0` into `S m`. -/
theorem downChain_adjoint_mem {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j))
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0, LinearMap.adjoint (downChain T m) x ∈ S m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    show LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x ∈ S 0
    rw [LinearMap.adjoint_id]
    exact hx
  | succ m ih =>
    intro x hx
    rw [downChain_adjoint_succ]
    exact hS m _ (ih x hx)

/-- **Exact Rallis Chain Scalar Recursion (`ChainScalar`)**:
if each step satisfies `T j ((T j)* x) = c j • x` on `S j` and `(T j)* (S j) ⊆ S (j + 1)`, then
`downChain T m ((downChain T m)* x) = (∏ j ∈ range m, c j) • x` for all `x ∈ S 0`. -/
theorem chain_rallis_scalar_recursion {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜)
    (hstep : ∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x)
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0,
      downChain T m (LinearMap.adjoint (downChain T m) x) =
        (∏ j ∈ Finset.range m, c j) • x := by
  intro m
  induction m with
  | zero =>
    intro x _
    show LinearMap.id (LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x) = _
    rw [LinearMap.adjoint_id]
    simp
  | succ m ih =>
    intro x hx
    rw [downChain_adjoint_succ]
    show downChain T m (T m (LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x))) = _
    rw [hstep m _ (downChain_adjoint_mem T S hS m x hx), map_smul, ih x hx, smul_smul,
      Finset.prod_range_succ, mul_comm]

/-- **Exact Multiplicative Norm-Square Recursion Along `j = 0, ..., m`**:
under the step-wise Rallis scalar identity on `S j`, the norm-square of the `m`-step upward
theta lift `(downChain T m)* x` is the exact product of the step Rallis factors times `‖x‖^2`. -/
theorem chain_normSq_recursion {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜)
    (hstep : ∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x)
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1))
    (m : ℕ) {x : E 0} (hx : x ∈ S 0) :
    ‖LinearMap.adjoint (downChain T m) x‖ ^ 2 =
      (∏ j ∈ Finset.range m, RCLike.re (c j)) * ‖x‖ ^ 2 := by
  induction m with
  | zero =>
    show ‖LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x‖ ^ 2 = _
    rw [LinearMap.adjoint_id]
    simp
  | succ m ih =>
    set y : E m := LinearMap.adjoint (downChain T m) x
    have hy : y ∈ S m := downChain_adjoint_mem T S hS m x hx
    have hstep_norm : ‖LinearMap.adjoint (T m) y‖ ^ 2 = RCLike.re (c m) * ‖y‖ ^ 2 := by
      have hinner : inner 𝕜 (LinearMap.adjoint (T m) y) (LinearMap.adjoint (T m) y) =
          c m * inner 𝕜 y y := by
        rw [LinearMap.adjoint_inner_left, hstep m y hy, inner_smul_right]
      have hre := congrArg RCLike.re hinner
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
      rw [show ((‖LinearMap.adjoint (T m) y‖ : 𝕜) ^ 2) =
            ((‖LinearMap.adjoint (T m) y‖ ^ 2 : ℝ) : 𝕜) by norm_cast,
          show ((‖y‖ : 𝕜) ^ 2) = ((‖y‖ ^ 2 : ℝ) : 𝕜) by norm_cast,
          RCLike.ofReal_re, RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im,
          mul_zero, sub_zero] at hre
      exact hre
    rw [downChain_adjoint_succ, hstep_norm, ih, Finset.prod_range_succ]
    ring

/-- **Additive Log-Norm / Slope Decomposition Along `j = 0, ..., m`**
(feeding directly into Arakelov slope / `p`-adic divisibility accounting in `@rebuild-divisibility`
and `@rebuild-theta-slope`): when every step factor `Re (c j) > 0` and `x ≠ 0`,
`log ‖(downChain T m)* x‖^2 = log ‖x‖^2 + ∑ j < m, log (Re (c j))`. -/
theorem chain_log_normSq_additive {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜)
    (hstep : ∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x)
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1))
    (m : ℕ) (hc : ∀ j < m, 0 < RCLike.re (c j))
    {x : E 0} (hx : x ∈ S 0) (hx0 : x ≠ 0) :
    Real.log (‖LinearMap.adjoint (downChain T m) x‖ ^ 2) =
      Real.log (‖x‖ ^ 2) + ∑ j ∈ Finset.range m, Real.log (RCLike.re (c j)) := by
  rw [chain_normSq_recursion T S c hstep hS m hx]
  have hprod_pos : 0 < ∏ j ∈ Finset.range m, RCLike.re (c j) :=
    Finset.prod_pos fun j hj => hc j (Finset.mem_range.mp hj)
  have hx_pos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  rw [Real.log_mul hprod_pos.ne' hx_pos.ne',
    Real.log_prod (fun j hj => (hc j (Finset.mem_range.mp hj)).ne'), add_comm]

/-- **Definite-Chain Nonvanishing Induction**:
if every step Rallis factor `c j` is nonzero for `j < m`, then for every nonzero `x ∈ S 0`,
every intermediate lift `(downChain T j)* x` (`j ≤ m`) is nonzero and lies in `S j`. -/
theorem definite_chain_nonvanishing {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
    [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜)
    (hstep : ∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x)
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1))
    (m : ℕ) (hc : ∀ j < m, c j ≠ 0) {x : E 0} (hx : x ∈ S 0) (hx0 : x ≠ 0) :
    ∀ j ≤ m, LinearMap.adjoint (downChain T j) x ∈ S j ∧
      LinearMap.adjoint (downChain T j) x ≠ 0 := by
  intro j hj
  refine ⟨downChain_adjoint_mem T S hS j x hx, ?_⟩
  intro hz
  have hrec := chain_rallis_scalar_recursion T S c hstep hS j x hx
  rw [hz, map_zero] at hrec
  have hprod_ne : (∏ i ∈ Finset.range j, c i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => hc i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)
  exact hx0 ((smul_eq_zero.mp hrec.symm).resolve_left hprod_ne)

/-- Rank-stepped finite-dimensional normed-space family indexed by `R.chainRank j`. -/
structure RankSteppedChain (R : ChainRanks) where
  E : ℕ → Type
  [normed : ∀ j, NormedAddCommGroup (E j)]
  [space : ∀ j, NormedSpace ℂ (E j)]
  [fd : ∀ j, FiniteDimensional ℂ (E j)]
  dim_eq : ∀ j, j ≤ R.m → Module.finrank ℂ (E j) = R.chainRank j

attribute [instance] RankSteppedChain.normed RankSteppedChain.space RankSteppedChain.fd

/-- **Operator-Norm Stability Recursion for `chainOpM`** on a rank-stepped normed family:
if at each step `j < m`, the total weight norm satisfies `∑ i, ‖w j i‖ ≤ W j` and each kernel
component satisfies `‖K j i y v‖ ≤ B j * ‖v‖`, then `chainOpM w K m` amplifies the supremum norm
by at most `∏ j ∈ range m, (W j * B j)`. -/
theorem chainOpM_norm_le {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]
    (w : ∀ j, ι j → ℂ) (K : ∀ j, ι j → ι (j + 1) → (E j →ₗ[ℂ] E (j + 1)))
    (W B : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j) (hB : ∀ j, 0 ≤ B j)
    (hw : ∀ j, ∑ i : ι j, ‖w j i‖ ≤ W j)
    (hK : ∀ j a b (v : E j), ‖K j a b v‖ ≤ B j * ‖v‖)
    (f : ι 0 → E 0) (M0 : ℝ) (hM0 : 0 ≤ M0) (hf : ∀ i, ‖f i‖ ≤ M0) :
    ∀ (m : ℕ) (y : ι m),
      ‖chainOpM w K m f y‖ ≤ (∏ j ∈ Finset.range m, (W j * B j)) * M0 := by
  intro m
  induction m with
  | zero =>
    intro y
    simpa using hf y
  | succ m ih =>
    intro y
    rw [chainOpM_succ, kerOpM, Finset.prod_range_succ]
    set P : ℝ := ∏ j ∈ Finset.range m, (W j * B j)
    have hP : 0 ≤ P := Finset.prod_nonneg fun j _ => mul_nonneg (hW j) (hB j)
    calc
      ‖∑ i : ι m, w m i • K m i y (chainOpM w K m f i)‖
          ≤ ∑ i : ι m, ‖w m i • K m i y (chainOpM w K m f i)‖ := norm_sum_le _ _
      _ = ∑ i : ι m, ‖w m i‖ * ‖K m i y (chainOpM w K m f i)‖ := by
            simp_rw [norm_smul]
      _ ≤ ∑ i : ι m, ‖w m i‖ * (B m * (P * M0)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact le_trans (hK m i y _) (mul_le_mul_of_nonneg_left (ih i) (hB m))
      _ = (∑ i : ι m, ‖w m i‖) * (B m * (P * M0)) := (Finset.sum_mul _ _ _).symm
      _ ≤ W m * (B m * (P * M0)) :=
            mul_le_mul_of_nonneg_right (hw m) (mul_nonneg (hB m) (mul_nonneg hP hM0))
      _ = P * (W m * B m) * M0 := by ring

/-- Specialized rank-stepped norm recursion on a `RankSteppedChain R` carrying explicit dimension
`Module.finrank ℂ (X.E j) = R.k + j * (R.t + 1)` at every stage `j ≤ R.m`. -/
theorem rankStepped_chainOpM_norm_le {R : ChainRanks} (X : RankSteppedChain R)
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    (w : ∀ j, ι j → ℂ) (K : ∀ j, ι j → ι (j + 1) → (X.E j →ₗ[ℂ] X.E (j + 1)))
    (W B : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j) (hB : ∀ j, 0 ≤ B j)
    (hw : ∀ j, ∑ i : ι j, ‖w j i‖ ≤ W j)
    (hK : ∀ j a b (v : X.E j), ‖K j a b v‖ ≤ B j * ‖v‖)
    (f : ι 0 → X.E 0) (M0 : ℝ) (hM0 : 0 ≤ M0) (hf : ∀ i, ‖f i‖ ≤ M0) :
    (∀ j ≤ R.m, Module.finrank ℂ (X.E j) = R.k + j * (R.t + 1)) ∧
    (∀ j ≤ R.m, ∀ y : ι j,
      ‖chainOpM w K j f y‖ ≤ (∏ i ∈ Finset.range j, (W i * B i)) * M0) :=
  ⟨fun j hj => X.dim_eq j hj,
   fun j _ y => chainOpM_norm_le w K W B hW hB hw hK f M0 hM0 hf j y⟩

end ChainNormAndStability

end

end RHDirect.RallisSeesaw
