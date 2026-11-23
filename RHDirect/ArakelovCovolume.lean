import RHDirect.Interfaces
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# RHDirect.ArakelovCovolume

Compact, self-contained, 0-`sorry`, 0-`axiom` Lean 4 formalization of the **Bost Arakelov Slope
Inequality & Covolume Comparison Core** against `RHDirect.Interfaces` and Mathlib `v4.33.1`.

## Contents

1. **Euclidean / Hermitian Normed Lattices, Covolume, Arakelov Degree & Slopes**:
   - Discrete `ℤ`-lattices `L : Submodule ℤ E` inside finite-dimensional inner product spaces `E`,
     rank `rk L`, Gram covolume `covol L = √det(Gram(b))`, Arakelov degree `degAr L = -log(covol L)`,
     arithmetic slope `slope L = degAr L / rk L`, and maximal slope `muMax L = sSup (slopes L)`.
   - Basis-independence (`covol_eq_sqrt_det_gram`), positivity (`covol_pos`), base values
     (`covol_bot`, `covol_span_singleton`, `slope_span_singleton`), and full-rank sublattice
     index / Hilbert–Samuel Gram comparison (`covol_le_of_le_same_rank`, `covol_le_sqrt_det_gram`).

2. **Spectral Gram Determinant Contraction & Boundedness of Slopes**:
   - Pure finite-dimensional spectral proof of `gram_det_le` (`det(Gram w) ≤ C^(2n) det(Gram v)`
     via orthonormal change of basis and eigenvalue bounds `0 ≤ λ_k ≤ C²` — zero measure-theory
     overhead!).
   - Proof of `slopes_bddAbove`, `slope_le_muMax`, and monotonicity `muMax_mono`.

3. **Bost's Arakelov Slope Inequality & Divisibility / Product-Formula Forms**:
   - `bost_slope_inequality`: For any injective `φ : L →ₗ[ℤ] M` (`L ≠ ⊥`) with `‖φ x‖ ≤ C * ‖x‖`,
     `slope L ≤ muMax M + log C`.
   - `bost_degree_inequality`: `degAr L ≤ rk L * (muMax M + log C)`.
   - `bost_slope_inequality_divisible` & `bost_degree_inequality_divisible`: Product-formula /
     non-archimedean divisibility form when `φ(L) ⊆ D • M` (`D ≥ 1`):
     `slope L + log D ≤ muMax M + log C`.
   - `bost_rank_bound_of_divisible` & `bost_vanishing_criterion`: Sharp upper bound on `rk L` and
     vanishing criterion `rk L = 0` when non-archimedean divisibility beats the archimedean
     covolume + target maximal-slope budget.

4. **Corank Share, Layer-Cake Integration & Direct Deduction of `RHDirect.BostSlopeFiber.SlopeIneq`**:
   - `corank_share_bound` & `weighted_corank_share_bound` (Markov / spread tail bound).
   - `layer_cake_slope_integral` & `integral_four_uF_div_add` (`∫₀^H 4 u / (u + τ) dτ = 4 u log(1 + H/u)`).
   - `bostSlopeFiber_slopeIneq_of_tail_bound` & `bostSlopeFiber_slopeIneq_of_corank_frame`:
     Direct, verbatim deduction of `RHDirect.BostSlopeFiber.SlopeIneq` (`MeanBoundSecondForm.lean`).
   - `bostSlopeFiber_covolume_comparison` & `bostSlopeFiber_exceptional_rank_bound`:
     Archimedean covolume vs. non-archimedean divisibility comparison on a `BostSlopeFiber`.
-/

open Module Submodule Finset Real MeasureTheory
open scoped BigOperators Matrix

namespace RHDirect.ArakelovCovolume

noncomputable section

/-! ## Section 1: Normed Lattices, Gram Covolume, Arakelov Degree & Slopes -/

/-- Discrete topology passes to any `ℤ`-sublattice `N ≤ L`. -/
lemma discreteTopology_of_le {E : Type*} [NormedAddCommGroup E]
    {L N : Submodule ℤ E} [DiscreteTopology L] (hNL : N ≤ L) :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (continuous_inclusion hNL)
    (Submodule.inclusion_injective hNL)

/-- Gram matrix transformation under linear change of vectors `w_j = ∑_i P_{ij} v_i`. -/
theorem gram_sum_smul_eq_transpose_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] (v : ι → E) (P : Matrix ι κ ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, P i j • v i) = P.transpose * Matrix.gram ℝ v * P := by
  ext j k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

section LatticeDefs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Rank of a `ℤ`-lattice `L ⊂ E`. -/
def rk (L : Submodule ℤ E) : ℕ := Module.finrank ℤ L

open Classical in
/-- Euclidean / Hermitian covolume `√(det Gram(b))` of a discrete `ℤ`-lattice `L ⊂ E`. -/
def covol (L : Submodule ℤ E) : ℝ :=
  if h : DiscreteTopology L then
    haveI := h
    Real.sqrt (Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L i : L) : E))).det
  else 0

/-- Arakelov degree `deg_Ar(L) = -log covol(L)`. -/
def degAr (L : Submodule ℤ E) : ℝ := -Real.log (covol L)

/-- Arithmetic slope `μ(L) = deg_Ar(L) / rank(L)`. -/
def slope (L : Submodule ℤ E) : ℝ := degAr L / (rk L : ℝ)

/-- Set of slopes of nonzero `ℤ`-sublattices `N ≤ L`. -/
def slopes (L : Submodule ℤ E) : Set ℝ :=
  { t | ∃ N : Submodule ℤ E, N ≤ L ∧ N ≠ ⊥ ∧ slope N = t }

/-- Maximal arithmetic slope `μ_max(L) = sup_{0 ≠ N ≤ L} μ(N)`. -/
def muMax (L : Submodule ℤ E) : ℝ := sSup (slopes L)

omit [FiniteDimensional ℝ E] in
/-- The Gram determinant of any two finite `ℤ`-bases of `L` is equal (`det M ∈ {±1}`). -/
theorem det_gram_basis_eq (L : Submodule ℤ E)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℤ L) (c : Basis κ ℤ L) :
    (Matrix.gram ℝ (fun i => (b i : E))).det = (Matrix.gram ℝ (fun k => (c k : E))).det := by
  let e : ι ≃ κ := b.indexEquiv c
  let c' : Basis ι ℤ L := c.reindex e.symm
  have hc' : (Matrix.gram ℝ (fun k => (c k : E))).det =
      (Matrix.gram ℝ (fun i => (c' i : E))).det := by
    have hs : Matrix.gram ℝ (fun i => (c' i : E)) =
        (Matrix.gram ℝ (fun k => (c k : E))).submatrix e e := by
      ext i j
      simp [c', Matrix.gram_apply]
    rw [hs, Matrix.det_submatrix_equiv_self]
  rw [hc']
  let M : Matrix ι ι ℤ := c'.toMatrix b
  have hb : (fun i => (b i : E)) =
      fun i => ∑ k, (M.map (Int.cast : ℤ → ℝ)) k i • (c' k : E) := by
    funext i
    conv_lhs => rw [← c'.sum_repr (b i)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Matrix.map_apply, Int.cast_smul_eq_zsmul]
    rfl
  rw [hb, gram_sum_smul_eq_transpose_mul (fun k => (c' k : E)) (M.map (Int.cast : ℤ → ℝ)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det ^ 2 = 1 := by
    have h2 : M.det * (b.toMatrix c').det = 1 := by
      rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip c' b, Matrix.det_one]
    have h3 : IsUnit M.det :=
      ⟨⟨M.det, (b.toMatrix c').det, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    rw [← Int.cast_det]
    rcases Int.isUnit_iff.1 h3 with h | h <;> rw [h] <;> norm_num
  linear_combination (Matrix.gram ℝ (fun i => (c' i : E))).det * hdet

/-- **Basis-independence of covolume**: for any `ℤ`-basis `b` of a discrete lattice `L`,
`covol L = √(det Gram(b))`. -/
theorem covol_eq_sqrt_det_gram (L : Submodule ℤ E) [hL : DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
  classical
  unfold covol
  rw [dif_pos hL]
  congr 1
  exact det_gram_basis_eq L (Module.finBasis ℤ L) b

/-- For a discrete `ℤ`-submodule `L ⊂ E`, its `ℤ`-rank equals the `ℝ`-dimension of its `ℝ`-span. -/
theorem finrank_int_eq_finrank_real_span (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
  let V := Submodule.span ℝ (L : Set E)
  let L₀ : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let e : L₀ ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : DiscreteTopology L₀ :=
    DiscreteTopology.of_continuous_injective
      (f := e) (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      e.injective
  have : IsZLattice ℝ L₀ := ⟨Submodule.span_span_coe_preimage⟩
  rw [← e.finrank_eq, ZLattice.rank ℝ L₀]

/-- Any `ℤ`-basis of a discrete lattice `L ⊂ E` is `ℝ`-linearly independent in `E`. -/
theorem linearIndependent_coe_basis (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    LinearIndependent ℝ (fun i => (b i : E)) := by
  have hspanZ : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hspanR : Submodule.span ℝ (Set.range fun i => (b i : E)) = Submodule.span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (b i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR,
    ← finrank_int_eq_finrank_real_span L, Module.finrank_eq_card_basis b]

/-- The Gram determinant of any `ℤ`-basis of a discrete lattice is strictly positive. -/
theorem det_gram_basis_pos (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    0 < (Matrix.gram ℝ (fun i => (b i : E))).det :=
  (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L b)).det_pos

/-- Every discrete `ℤ`-lattice has strictly positive covolume. -/
theorem covol_pos (L : Submodule ℤ E) [hL : DiscreteTopology L] : 0 < covol L := by
  classical
  rw [covol, dif_pos hL]
  exact Real.sqrt_pos.mpr (det_gram_basis_pos L _)

/-- A nonzero discrete `ℤ`-lattice has strictly positive rank. -/
theorem rk_pos_of_ne_bot (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) : 0 < rk L := by
  have : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hL
  exact Module.finrank_pos

/-- The zero lattice has covolume `1` and Arakelov degree `0`. -/
theorem covol_bot : covol (⊥ : Submodule ℤ E) = 1 := by
  let b0 : Basis (Fin 0) ℤ (⊥ : Submodule ℤ E) :=
    Basis.mk (v := Fin.elim0) linearIndependent_empty_type (by
      intro x _
      have hx : x = 0 := Subsingleton.elim x 0
      rw [hx]
      exact Submodule.zero_mem _)
  rw [covol_eq_sqrt_det_gram (⊥ : Submodule ℤ E) b0, Matrix.det_isEmpty, Real.sqrt_one]

theorem degAr_bot : degAr (⊥ : Submodule ℤ E) = 0 := by
  simp [degAr, covol_bot]

/-- A rank-1 lattice `ℤ · v` (`v ≠ 0`) has covolume `‖v‖`, degree `-log ‖v‖`, and slope `-log ‖v‖`. -/
theorem covol_span_singleton {v : E} (hv : v ≠ 0) :
    covol (Submodule.span ℤ ({v} : Set E)) = ‖v‖ := by
  let L : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  let e : ℤ ≃ₗ[ℤ] L :=
    { toFun := fun n => ⟨n • v, Submodule.smul_mem _ n (Submodule.subset_span rfl)⟩
      invFun := fun x => Classical.choose (Submodule.mem_span_singleton.mp x.2)
      map_add' := fun m n => Subtype.ext (add_zsmul v m n)
      map_smul' := fun m n => Subtype.ext (by simp [mul_zsmul])
      left_inv := fun n => by
        have hc := Classical.choose_spec
          (Submodule.mem_span_singleton.mp (Submodule.smul_mem L n (Submodule.subset_span rfl)))
        have hsub : ((Classical.choose
          (Submodule.mem_span_singleton.mp (Submodule.smul_mem L n (Submodule.subset_span rfl)))
            - n : ℤ) : ℝ) • v = 0 := by
          rw [Int.cast_sub, sub_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, hc, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | h0
        · exact sub_eq_zero.mp (by exact_mod_cast h0)
        · exact absurd h0 hv
      right_inv := fun x => Subtype.ext
        (Classical.choose_spec (Submodule.mem_span_singleton.mp x.2)) }
  have : DiscreteTopology L := by
    have hcont : Continuous (fun x : L => (inner ℝ v (x : E)) / ‖v‖ ^ 2) :=
      (continuous_const.inner continuous_subtype_val).div_const _
    have hinv : ∀ x : L, (e.symm x : ℝ) = inner ℝ v (x : E) / ‖v‖ ^ 2 := by
      intro x
      have hx : (x : E) = (e.symm x : ℤ) • v := by
        have := congrArg Subtype.val (e.apply_symm_apply x)
        exact this.symm
      rw [hx, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
      field_simp [hvn]
    refine DiscreteTopology.of_continuous_injective (f := fun x : L => (e.symm x : ℤ)) ?_
      e.symm.injective
    have hcast : Continuous (fun x : L => ((e.symm x : ℤ) : ℝ)) := by
      simpa only [funext hinv] using hcont
    exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hcast
  let b : Basis (Fin 1) ℤ L := (Basis.singleton (Fin 1) ℤ).map e
  rw [covol_eq_sqrt_det_gram L b]
  have hb0 : (b 0 : E) = v := by simp [b, e]
  have hdet : (Matrix.gram ℝ (fun i : Fin 1 => (b i : E))).det = ‖v‖ ^ 2 := by
    rw [Matrix.det_fin_one, Matrix.gram_apply, hb0, real_inner_self_eq_norm_sq]
  rw [hdet, Real.sqrt_sq (norm_nonneg v)]

theorem slope_span_singleton {v : E} (hv : v ≠ 0) :
    slope (Submodule.span ℤ ({v} : Set E)) = -Real.log ‖v‖ := by
  let L : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  have hrk : rk L = 1 := by
    unfold rk
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => (⟨v, Submodule.subset_span rfl⟩ : L)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 : g 0 • v = 0 := by
        have := congrArg Subtype.val hg
        simpa [Fin.sum_univ_one] using this
      have h1 : ((g 0 : ℤ) : ℝ) • v = 0 := by rwa [Int.cast_smul_eq_zsmul]
      rcases smul_eq_zero.mp h1 with h2 | h2
      · fin_cases i; exact_mod_cast h2
      · exact absurd h2 hv
    have hsp : ⊤ ≤ Submodule.span ℤ (Set.range fun _ : Fin 1 => (⟨v, Submodule.subset_span rfl⟩ : L)) := by
      intro x _
      obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp x.2
      have hx : x = n • (⟨v, Submodule.subset_span rfl⟩ : L) := Subtype.ext hn.symm
      rw [hx]
      exact Submodule.smul_mem _ n (Submodule.subset_span ⟨0, rfl⟩)
    let b : Basis (Fin 1) ℤ L := Basis.mk hli hsp
    simpa using Module.finrank_eq_card_basis b
  change degAr L / (rk L : ℝ) = -Real.log ‖v‖
  rw [hrk]
  simp [degAr, L, covol_span_singleton hv]

/-- **Full-rank sublattice covolume comparison (Hilbert–Samuel / index formula)**:
If `M ≤ L` are discrete `ℤ`-lattices of equal rank `rk M = rk L`, then there is an integer
change-of-basis matrix `P` with `P.det ≠ 0` and `covol M = |(P.det : ℝ)| * covol L`.
In particular `covol L ≤ covol M` and `degAr M ≤ degAr L`. -/
theorem covol_le_of_le_same_rank {L M : Submodule ℤ E} [DiscreteTopology L]
    (hML : M ≤ L) (hrk : rk M = rk L) :
    covol L ≤ covol M ∧ degAr M ≤ degAr L := by
  have : DiscreteTopology M := discreteTopology_of_le hML
  let bL : Basis (Fin (rk L)) ℤ L := Module.finBasis ℤ L
  let bM : Basis (Fin (rk L)) ℤ M := (Module.finBasis ℤ M).reindex (finCongr hrk)
  let P : Matrix (Fin (rk L)) (Fin (rk L)) ℤ :=
    fun i j => bL.repr ⟨(bM j : E), hML (bM j).2⟩ i
  have hEq : (fun j => (bM j : E)) =
      fun j => ∑ i, (P.map (Int.cast : ℤ → ℝ)) i j • (bL i : E) := by
    funext j
    have h := congrArg Subtype.val (bL.sum_repr ⟨(bM j : E), hML (bM j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.map_apply, Int.cast_smul_eq_zsmul]
  have hdet : (Matrix.gram ℝ (fun j => (bM j : E))).det =
      ((P.det : ℤ) : ℝ) ^ 2 * (Matrix.gram ℝ (fun i => (bL i : E))).det := by
    rw [hEq, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hcast : (P.map (Int.cast : ℤ → ℝ)).det = (P.det : ℝ) := (Int.cast_det P).symm
    rw [hcast]
    ring
  have hposM : 0 < (Matrix.gram ℝ (fun j => (bM j : E))).det := det_gram_basis_pos M bM
  have hposL : 0 < (Matrix.gram ℝ (fun i => (bL i : E))).det := det_gram_basis_pos L bL
  have hPne : P.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, zero_pow two_ne_zero, zero_mul] at hdet
    exact hposM.ne' hdet
  have hPge1 : (1 : ℝ) ≤ ((P.det : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ P.det ^ 2 := by
      have : 1 ≤ |P.det| := Int.one_le_abs hPne
      nlinarith [sq_abs P.det]
    exact_mod_cast h1
  have hcov : covol L ≤ covol M := by
    rw [covol_eq_sqrt_det_gram L bL, covol_eq_sqrt_det_gram M bM, hdet]
    exact Real.sqrt_le_sqrt (le_mul_of_one_le_left hposL.le hPge1)
  refine ⟨hcov, ?_⟩
  unfold degAr
  linarith [Real.log_le_log (covol_pos L) hcov]

/-- **Hilbert–Samuel Gram-Upper-Bound on Lattice Covolume** (`PCovolumeLeGram.lean`):
Any `rk L` vectors `x : ι → E` inside a discrete lattice `L` that are `ℝ`-linearly independent
satisfy `covol L ≤ √(det Gram(x))`. -/
theorem covol_le_sqrt_det_gram {L : Submodule ℤ E} [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → E)
    (hxL : ∀ i, x i ∈ L) (hli : LinearIndependent ℝ x) (hcard : Fintype.card ι = rk L) :
    covol L ≤ Real.sqrt (Matrix.gram ℝ x).det := by
  let M : Submodule ℤ E := Submodule.span ℤ (Set.range x)
  have hML : M ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hxL i)
  have : DiscreteTopology M := discreteTopology_of_le hML
  have hliZ : LinearIndependent ℤ (fun i => (⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩ : M)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ j, ((g j : ℤ) : ℝ) • x j = 0 := by
      have := congrArg Subtype.val hg
      simpa [Submodule.coe_sum, Int.cast_smul_eq_zsmul] using this
    exact_mod_cast Fintype.linearIndependent_iff.mp hli (fun j => (g j : ℝ)) h1 i
  have hsp : ⊤ ≤ Submodule.span ℤ
      (Set.range fun i => (⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩ : M)) := by
    intro y _
    have hy : (y : E) ∈ Submodule.span ℤ (Set.range x) := y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, hc⟩ := hy
    have hyeq : y = ∑ i, c i • (⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩ : M) :=
      Subtype.ext (by simpa [Submodule.coe_sum] using hc.symm)
    rw [hyeq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bM : Basis ι ℤ M := Basis.mk hliZ hsp
  have hrkM : rk M = rk L := by
    show Module.finrank ℤ M = rk L
    rw [Module.finrank_eq_card_basis bM, hcard]
  have hcovM : covol M = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [covol_eq_sqrt_det_gram M bM]
    congr 2
    ext i j
    simp [bM, Matrix.gram_apply]
  rw [← hcovM]
  exact (covol_le_of_le_same_rank hML hrkM).1

end LatticeDefs

/-! ## Section 2: Spectral Gram Determinant Contraction & Boundedness of Slopes -/

section SpectralGram

/-- **Spectral Gram Determinant Contraction (`gram_det_le`)**:
If `v : ι → E` and `w : ι → F` satisfy `‖∑ c_i w_i‖ ≤ C * ‖∑ c_i v_i‖` for all `c : ι → ℝ`, then
`det(Gram w) ≤ C ^ (2 * |ι|) * det(Gram v)`.
Proved directly via orthonormal change of basis + spectral theorem (`0 ≤ λ_k ≤ C²`) with zero
measure-theory overhead. -/
theorem gram_det_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → E) (w : ι → F) (C : ℝ)
    (hC : ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) :
    (Matrix.gram ℝ w).det ≤ C ^ (2 * Fintype.card ι) * (Matrix.gram ℝ v).det := by
  by_cases hv : LinearIndependent ℝ v
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Matrix.det_isEmpty]
    obtain ⟨i₀⟩ := hι
    have hC0 : 0 ≤ C := by
      have h1 := hC (Pi.single i₀ (1 : ℝ))
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] at h1
      have hv0 : 0 < ‖v i₀‖ := norm_pos_iff.mpr (hv.ne_zero i₀)
      by_contra hneg
      push Not at hneg
      nlinarith [norm_nonneg (w i₀)]
    let U : Submodule ℝ E := Submodule.span ℝ (Set.range v)
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
    let Bv : Basis ι ℝ U := Basis.span hv
    have hBv : ∀ i, (Bv i : E) = v i := fun i => congrArg Subtype.val (Basis.span_apply hv i)
    let T : U →ₗ[ℝ] F := Bv.constr ℝ w
    have hTBv : ∀ i, T (Bv i) = w i := fun i => Bv.constr_basis ℝ w i
    have hTbound : ∀ x : U, ‖T x‖ ≤ C * ‖x‖ := by
      intro x
      have hx : x = ∑ i, Bv.repr x i • Bv i := (Bv.sum_repr x).symm
      have hxE : (x : E) = ∑ i, Bv.repr x i • v i := by
        conv_lhs => rw [hx]
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, hBv]
      have hTx : T x = ∑ i, Bv.repr x i • w i := by
        conv_lhs => rw [hx]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hTBv]
      rw [hTx]
      simpa only [Submodule.coe_norm, hxE] using hC (fun i => Bv.repr x i)
    have hdim : Module.finrank ℝ U = Fintype.card ι := Module.finrank_eq_card_basis Bv
    let u : OrthonormalBasis ι ℝ U :=
      (stdOrthonormalBasis ℝ U).reindex (Fintype.equivOfCardEq (by simp [hdim]))
    let P : Matrix ι ι ℝ := u.toBasis.toMatrix Bv
    have hvP : v = fun j => ∑ k, P k j • (u k : E) := by
      funext j
      have h1 := congrArg Subtype.val (u.toBasis.sum_repr (Bv j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBv, OrthonormalBasis.coe_toBasis] at h1
      simpa [P, Module.Basis.toMatrix_apply] using h1.symm
    have hwP : w = fun j => ∑ k, P k j • T (u k) := by
      funext j
      have h1 := congrArg T (u.toBasis.sum_repr (Bv j))
      simp only [map_sum, map_smul, hTBv, OrthonormalBasis.coe_toBasis] at h1
      simpa [P, Module.Basis.toMatrix_apply] using h1.symm
    have hGramU : Matrix.gram ℝ (fun k => (u k : E)) = 1 := by
      ext i j
      rw [Matrix.gram_apply, Matrix.one_apply]
      have : inner ℝ (u i : E) (u j : E) = inner ℝ (u i) (u j) := rfl
      rw [this, orthonormal_iff_ite.mp u.orthonormal i j]
    have hdetV : (Matrix.gram ℝ v).det = P.det ^ 2 := by
      rw [hvP, gram_sum_smul_eq_transpose_mul, hGramU, Matrix.mul_one,
        Matrix.det_mul, Matrix.det_transpose, sq]
    let G : Matrix ι ι ℝ := Matrix.gram ℝ (fun k => T (u k))
    have hdetW : (Matrix.gram ℝ w).det = P.det ^ 2 * G.det := by
      rw [hwP, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose]
      ring
    have hGpsd : G.PosSemidef := Matrix.posSemidef_gram ℝ (fun k => T (u k))
    have hGherm : G.IsHermitian := hGpsd.isHermitian
    have hGdet : G.det ≤ C ^ (2 * Fintype.card ι) := by
      rw [hGherm.det_eq_prod_eigenvalues]
      have hpow : C ^ (2 * Fintype.card ι) = ∏ _k : ι, C ^ 2 := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      rw [hpow]
      refine Finset.prod_le_prod (fun k _ => hGpsd.eigenvalues_nonneg k) fun k _ => ?_
      let q : EuclideanSpace ℝ ι := hGherm.eigenvectorBasis k
      have hqnorm : ‖q‖ = 1 := hGherm.eigenvectorBasis.orthonormal.1 k
      have heig : hGherm.eigenvalues k = ∑ i, ∑ j, q i * G i j * q j := by
        have hmul := hGherm.mulVec_eigenvectorBasis k
        have h1 : inner ℝ q (WithLp.toLp 2 (G.mulVec q)) = hGherm.eigenvalues k := by
          have hvec : WithLp.toLp 2 (G.mulVec q) = (hGherm.eigenvalues k) • q := by
            ext i
            simpa [q] using congrFun hmul i
          rw [hvec, real_inner_smul_right, real_inner_self_eq_norm_sq, hqnorm, one_pow, mul_one]
        rw [← h1, EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.sum_mul, q]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      let xU : U := ∑ i, q i • u i
      have hxUnorm : ‖xU‖ = 1 := by
        have hsq : ‖xU‖ ^ 2 = 1 := by
          rw [← real_inner_self_eq_norm_sq, sum_inner]
          have hsum : ∑ i, inner ℝ (q i • u i) (∑ j, q j • u j) = ∑ i, (q i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [inner_sum]
            have hterm : ∑ j, inner ℝ (q i • u i) (q j • u j) =
                ∑ j, if i = j then (q i) ^ 2 else 0 := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp u.orthonormal i j]
              split_ifs with h <;> simp [h, sq]
            rw [hterm]
            simp
          rw [hsum]
          have hqn := real_inner_self_eq_norm_sq q
          rw [hqnorm, one_pow, EuclideanSpace.inner_eq_star_dotProduct] at hqn
          simpa [dotProduct, sq] using hqn
        have hnn : 0 ≤ ‖xU‖ := norm_nonneg xU
        nlinarith
      have hTxU : ‖T xU‖ ^ 2 = ∑ i, ∑ j, q i * G i j * q j := by
        rw [← real_inner_self_eq_norm_sq]
        have hTsum : T xU = ∑ i, q i • T (u i) := by simp [xU, map_sum, map_smul]
        rw [hTsum, sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_left, real_inner_smul_right]
        simp only [G, Matrix.gram_apply]
        ring
      rw [heig, ← hTxU]
      have hb := hTbound xU
      rw [hxUnorm, mul_one] at hb
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [hdetW, hdetV]
    nlinarith [sq_nonneg P.det]
  · rw [Fintype.linearIndependent_iff] at hv
    push Not at hv
    obtain ⟨c, hcv, i₀, hci₀⟩ := hv
    have hcw : ∑ i, c i • w i = 0 := by
      have h1 := hC c
      rw [hcv, norm_zero, mul_zero] at h1
      exact norm_le_zero_iff.mp h1
    have hdetW0 : (Matrix.gram ℝ w).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, fun h => hci₀ (congrFun h i₀), ?_⟩
      ext i
      have h1 : inner ℝ (w i) (∑ j, c j • w j) = 0 := by rw [hcw, inner_zero_right]
      rw [inner_sum] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1
    rw [hdetW0]
    have hpow0 : 0 ≤ C ^ (2 * Fintype.card ι) := by rw [pow_mul]; positivity
    exact mul_nonneg hpow0 (Matrix.posSemidef_gram ℝ v).det_nonneg

/-- Extend an operator-norm bound from `ℤ`-linear combinations to all `ℝ`-linear combinations by
clearing rational denominators and continuity on `ℚ^ι ⊂ ℝ^ι`. -/
theorem norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by
  have hq : ∀ q : ι → ℚ, ‖∑ i, (q i : ℝ) • w i‖ ≤ C * ‖∑ i, (q i : ℝ) • v i‖ := by
    intro q
    classical
    obtain ⟨m, hm, hz⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (q i : ℝ) * m = z := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), fun i => ?_⟩
      obtain ⟨k, hk⟩ : (q i).den ∣ ∏ j, (q j).den :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      rw [hk]
      push_cast
      rw [← mul_assoc]
      congr 1
      exact_mod_cast Rat.mul_den_eq_num (q i)
    choose n hn using hz
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hw : ∑ i, (n i : ℝ) • w i = (m : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have hv : ∑ i, (n i : ℝ) • v i = (m : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have key := h n
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hm'.le, mul_left_comm] at key
    exact le_of_mul_le_mul_left key hm'
  intro c
  have hd : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hd.induction_on (p := fun c : ι → ℝ => ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) c ?_ hq
  exact isClosed_le (by fun_prop) (by fun_prop)

private lemma gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp only [Matrix.gram_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
    Matrix.transpose_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    map_sum, map_mul, eq_intCast]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **Boundedness of Slopes**: The set `slopes L` of slopes of all nonzero sublattices of a
discrete `ℤ`-lattice `L` is bounded above, so `muMax L = sSup (slopes L)` is well-defined. -/
theorem slopes_bddAbove {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] :
    BddAbove (slopes L) := by
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis L e
  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => x i) hx
    ext i
    exact h0 i
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  have : DiscreteTopology N := discreteTopology_of_le hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simpa [M, Int.cast_smul_eq_zsmul] using h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := fun j => by rw [hfj j]; rfl
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := gram_det_le (fun j => (f j : E)) w K hcomp
  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : ∑ j, c j • (f j : E) = 0 := by
      have := congrArg S hc
      simpa [map_sum, map_smul, hSw] using this
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis N f) c h1 i
  have hwpos : 0 < (Matrix.gram ℝ w).det :=
    (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  have hint : (Matrix.gram ℝ w).det = (((M.transpose * M).det : ℤ) : ℝ) := by
    rw [gram_intMatrix_eq_map M, ← RingHom.map_det]
    rfl
  have h1le : (1 : ℝ) ≤ (Matrix.gram ℝ w).det := by
    rw [hint] at hwpos ⊢
    have hposZ : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast Int.add_one_le_iff.mpr hposZ
  have hcovN : covol N = Real.sqrt (Matrix.gram ℝ (fun j => (f j : E))).det :=
    covol_eq_sqrt_det_gram N f
  have hcov_lb : (1 : ℝ) ≤ (K : ℝ) ^ (rk N) * covol N := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) ^ (2 * rk N) * (Matrix.gram ℝ (fun j => (f j : E))).det := by
      simpa [rk, Fintype.card_fin] using h1le.trans hdet
    have hsq := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_one, show (K : ℝ) ^ (2 * rk N) = ((K : ℝ) ^ rk N) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), ← hcovN] at hsq
    exact hsq
  have hrpos : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast rk_pos_of_ne_bot N hN0
  have hlog : 0 ≤ (rk N : ℝ) * Real.log K + Real.log (covol N) := by
    have h := Real.log_le_log one_pos hcov_lb
    rw [Real.log_one, Real.log_mul (by positivity) (covol_pos N).ne', Real.log_pow] at h
    exact h
  unfold slope degAr
  rw [div_le_iff₀ hrpos]
  linarith

/-- Every nonzero sublattice `N ≤ L` has `slope N ≤ muMax L`. -/
theorem slope_le_muMax {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L N : Submodule ℤ E) [DiscreteTopology L]
    (hNL : N ≤ L) (hN0 : N ≠ ⊥) :
    slope N ≤ muMax L :=
  le_csSup (slopes_bddAbove L) ⟨N, hNL, hN0, rfl⟩

/-- Monotonicity of maximal slope: `N ≤ L` (`N ≠ ⊥`) implies `muMax N ≤ muMax L`. -/
theorem muMax_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L N : Submodule ℤ E) [DiscreteTopology L]
    (hNL : N ≤ L) (hN0 : N ≠ ⊥) :
    muMax N ≤ muMax L := by
  have : DiscreteTopology N := discreteTopology_of_le hNL
  exact csSup_le ⟨slope N, N, le_rfl, hN0, rfl⟩
    (fun _ ⟨K, hKN, hK0, ht⟩ => ht ▸ slope_le_muMax L K (hKN.trans hNL) hK0)

end SpectralGram

/-! ## Section 3: Bost's Arakelov Slope Inequality & Divisibility / Vanishing Criteria -/

section BostSlope

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Bost's Arakelov Slope Inequality** (`Formalism/LatticeSlopes/SlopeInequality.lean`):
For any injective `ℤ`-linear evaluation/restriction map `φ : L →ₗ[ℤ] M` between discrete
Hermitian/Euclidean lattices `L ⊂ E` (`L ≠ ⊥`) and `M ⊂ F` satisfying the operator norm bound
`‖φ(x)‖ ≤ C * ‖x‖`,
`slope L ≤ muMax M + log C`. -/
theorem bost_slope_inequality (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M] (hL0 : L ≠ ⊥)
    (φ : L →ₗ[ℤ] M) (C : ℝ) (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) :
    slope L ≤ muMax M + Real.log C := by
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by rintro _ ⟨x, rfl⟩; exact (φ x).2
  have : DiscreteTopology N := discreteTopology_of_le hNM
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
    intro h0
    apply hx0
    have h1 : φ ⟨x, hxL⟩ = φ 0 := by rw [map_zero]; exact Subtype.ext h0
    exact congrArg Subtype.val (hφ h1)
  have hN0 : N ≠ ⊥ := by
    intro h0
    apply hφx
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g _
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hCpos : 0 < C := by
    have h1 := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have h1 : slope N ≤ muMax M := slope_le_muMax M N hNM hN0
  set r := rk L
  have hrkN : rk N = r := e.finrank_eq.symm
  have hrpos : 0 < r := rk_pos_of_ne_bot L hL0
  let b := Module.finBasis ℤ L
  have hcL : covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det :=
    covol_eq_sqrt_det_gram L b
  have hcN : covol N = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det :=
    covol_eq_sqrt_det_gram N (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  have hdet := gram_det_le (fun i => (b i : E)) (fun i => ((φ (b i) : M) : F)) C hreal
  have hle : covol N ≤ C ^ r * covol L := by
    rw [hcN, hcL]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : E))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hlog : Real.log (covol N) ≤ r * Real.log C + Real.log (covol L) := by
    have h2 := Real.log_le_log (covol_pos N) hle
    rwa [Real.log_mul (by positivity) (covol_pos L).ne', Real.log_pow] at h2
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope degAr
    rw [hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    nlinarith
  linarith

/-- **Arakelov Degree Form of Bost's Slope Inequality** (holds unconditionally, including `L = ⊥`):
`deg_Ar(L) ≤ rank(L) * (μ_max(M) + log C)`. -/
theorem bost_degree_inequality (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    (φ : L →ₗ[ℤ] M) (C : ℝ) (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖) :
    degAr L ≤ (rk L : ℝ) * (muMax M + Real.log C) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have hrk0 : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [degAr_bot, hrk0]
    simp
  · have h := bost_slope_inequality L M hL0 φ C hφ hC
    have hrpos : (0 : ℝ) < (rk L : ℝ) := by exact_mod_cast rk_pos_of_ne_bot L hL0
    exact (div_le_iff₀ hrpos).mp h |>.trans_eq (mul_comm _ _)

/-- **Product-Formula / Non-Archimedean Divisibility Bost Slope Inequality**:
If `φ : L →ₗ[ℤ] M` (`L ≠ ⊥`) is injective with archimedean bound `‖φ x‖ ≤ C * ‖x‖` AND its image is
divisible by `D ≥ 1` inside `M` (`∀ x, ∃ y ∈ M, φ x = D • y`, encoding non-archimedean valuation
gain `log D`), then:
`slope L + log D ≤ muMax M + log C`. -/
theorem bost_slope_inequality_divisible (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M] (hL0 : L ≠ ⊥)
    (φ : L →ₗ[ℤ] M) (C : ℝ) (D : ℕ) (hD : 0 < D) (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : L, ∃ y : M, φ x = (D : ℤ) • y) :
    slope L + Real.log (D : ℝ) ≤ muMax M + Real.log C := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  choose ψ hψ using hDiv
  have hψ_val : ∀ x : L, ((ψ x : M) : F) = (D : ℝ)⁻¹ • ((φ x : M) : F) := by
    intro x
    have h1 : ((φ x : M) : F) = (D : ℝ) • ((ψ x : M) : F) := by
      have h2 := congrArg Subtype.val (hψ x)
      rw [Submodule.coe_smul] at h2
      rwa [← Int.cast_smul_eq_zsmul ℝ (D : ℤ), Int.cast_natCast] at h2
    rw [h1, inv_smul_smul₀ hDne]
  let ψLin : L →ₗ[ℤ] M :=
    { toFun := ψ
      map_add' := fun x y => by
        apply Subtype.ext
        rw [Submodule.coe_add, hψ_val, hψ_val, hψ_val, map_add, Submodule.coe_add, smul_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        change ((ψ (r • x) : M) : F) = r • ((ψ x : M) : F)
        rw [hψ_val, hψ_val, map_smul, Submodule.coe_smul,
          ← Int.cast_smul_eq_zsmul ℝ r, ← Int.cast_smul_eq_zsmul ℝ r, smul_comm] }
  have hψinj : Function.Injective ψLin := by
    intro x y hxy
    apply hφ
    rw [hψ x, hψ y]
    exact congrArg ((D : ℤ) • ·) hxy
  have hψC : ∀ x : L, ‖((ψLin x : M) : F)‖ ≤ (C / (D : ℝ)) * ‖(x : E)‖ := by
    intro x
    change ‖((ψ x : M) : F)‖ ≤ (C / (D : ℝ)) * ‖(x : E)‖
    rw [hψ_val, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hDpos), div_eq_inv_mul,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC x) (inv_nonneg.mpr hDpos.le)
  have hCpos : 0 < C := by
    obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
    have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
      intro h0
      apply hx0
      exact congrArg Subtype.val (hφ ((Subtype.ext h0).trans (map_zero φ).symm))
    have h1 := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have hBost := bost_slope_inequality L M hL0 ψLin (C / (D : ℝ)) hψinj hψC
  rw [Real.log_div hCpos.ne' hDne] at hBost
  linarith

/-- **Degree Form of Divisible Bost Inequality** (holds including `L = ⊥`):
`deg_Ar(L) + rk(L) * log D ≤ rk(L) * (μ_max(M) + log C)`. -/
theorem bost_degree_inequality_divisible (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    (φ : L →ₗ[ℤ] M) (C : ℝ) (D : ℕ) (hD : 0 < D) (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : L, ∃ y : M, φ x = (D : ℤ) • y) :
    degAr L + (rk L : ℝ) * Real.log (D : ℝ) ≤ (rk L : ℝ) * (muMax M + Real.log C) := by
  by_cases hL0 : L = ⊥
  · subst hL0
    have hrk0 : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    rw [degAr_bot, hrk0]
    simp
  · have h := bost_slope_inequality_divisible L M hL0 φ C D hD hφ hC hDiv
    have hrpos : (0 : ℝ) < (rk L : ℝ) := by exact_mod_cast rk_pos_of_ne_bot L hL0
    have hmul := mul_le_mul_of_nonneg_left h hrpos.le
    have hEq : (rk L : ℝ) * (slope L + Real.log (D : ℝ)) =
        degAr L + (rk L : ℝ) * Real.log (D : ℝ) := by
      unfold slope
      field_simp [hrpos.ne']
    linarith

/-- **Sharp Rank Upper Bound from Covolume vs. Divisibility**:
When non-archimedean divisibility `log D` strictly exceeds the target slope + archimedean norm
budget `M_max + log C`, and `covol L ≤ exp(C_arch)`, the rank of `L` is explicitly bounded by:
`rk L ≤ C_arch / (log D - M_max - log C)`. -/
theorem bost_rank_bound_of_divisible (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    (φ : L →ₗ[ℤ] M) (C M_max C_arch : ℝ) (D : ℕ) (hD : 0 < D)
    (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : L, ∃ y : M, φ x = (D : ℤ) • y)
    (hMmax : muMax M ≤ M_max)
    (hCov : covol L ≤ Real.exp C_arch)
    (hGap : 0 < Real.log (D : ℝ) - M_max - Real.log C) :
    (rk L : ℝ) ≤ C_arch / (Real.log (D : ℝ) - M_max - Real.log C) := by
  have hdeg := bost_degree_inequality_divisible L M φ C D hD hφ hC hDiv
  have hArch : -C_arch ≤ degAr L := by
    unfold degAr
    have h1 := Real.log_le_log (covol_pos L) hCov
    rw [Real.log_exp] at h1
    linarith
  have hrnn : (0 : ℝ) ≤ (rk L : ℝ) := Nat.cast_nonneg _
  rw [le_div_iff₀ hGap]
  nlinarith [mul_le_mul_of_nonneg_left hMmax hrnn]

/-- **Arakelov Vanishing Criterion**:
If a discrete lattice `L` with `covol L ≤ 1` (`0 ≤ deg_Ar(L)`) injects into `M` with archimedean
operator bound `C` and non-archimedean divisibility `D ≥ 1` satisfying `μ_max(M) + log C < log D`,
then `L = ⊥` and `rk L = 0`. -/
theorem bost_vanishing_criterion (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    (φ : L →ₗ[ℤ] M) (C : ℝ) (D : ℕ) (hD : 0 < D)
    (hφ : Function.Injective φ)
    (hC : ∀ x : L, ‖((φ x : M) : F)‖ ≤ C * ‖(x : E)‖)
    (hDiv : ∀ x : L, ∃ y : M, φ x = (D : ℤ) • y)
    (hCov : covol L ≤ 1)
    (hStrict : muMax M + Real.log C < Real.log (D : ℝ)) :
    L = ⊥ ∧ rk L = 0 := by
  have hL0 : L = ⊥ := by
    by_contra hne
    have hdeg := bost_slope_inequality_divisible L M hne φ C D hD hφ hC hDiv
    have hslope_nn : 0 ≤ slope L := by
      unfold slope degAr
      have hlog : Real.log (covol L) ≤ 0 := by
        simpa [Real.log_one] using Real.log_le_log (covol_pos L) hCov
      exact div_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  refine ⟨hL0, ?_⟩
  subst hL0
  simp [rk]

end BostSlope

/-! ## Section 4: Corank Share, Layer-Cake Integration & `RHDirect.BostSlopeFiber.SlopeIneq` -/

section LayerCakeAndBostFiber

/-- **Corank-Share Spread Bound** (`StatementFR.CorankShare`):
If `x : Fin R → ℝ` has average `≥ s` and upper spread `x j ≤ s + u` (`u > 0`), then for every
`τ ≥ 0`, the number of slopes strictly below `s - τ` is at most `(u / (u + τ)) * R`. -/
theorem corank_share_bound {R : ℕ} (x : Fin R → ℝ) (s u τ : ℝ)
    (hu : 0 < u) (hτ : 0 ≤ τ)
    (hmean : (R : ℝ) * s ≤ ∑ j, x j)
    (hup : ∀ j, x j ≤ s + u) :
    ((Finset.univ.filter fun j => x j < s - τ).card : ℝ) ≤ (u / (u + τ)) * (R : ℝ) := by
  set B := Finset.univ.filter fun j => x j < s - τ
  have hsplit : ∑ j : Fin R, x j = (∑ j ∈ B, x j) + (∑ j ∈ Bᶜ, x j) := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have hB : ∑ j ∈ B, x j ≤ (B.card : ℝ) * (s - τ) := by
    calc ∑ j ∈ B, x j ≤ ∑ _j ∈ B, (s - τ) :=
          Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.le
      _ = (B.card : ℝ) * (s - τ) := by simp; ring
  have hBc_card : (Bᶜ.card : ℝ) = (R : ℝ) - (B.card : ℝ) := by
    have h1 : B.card + Bᶜ.card = R := by
      rw [← Finset.card_union_of_disjoint disjoint_compl_right, Finset.union_compl,
        Finset.card_univ, Fintype.card_fin]
    have h1' : (B.card : ℝ) + (Bᶜ.card : ℝ) = (R : ℝ) := by exact_mod_cast h1
    linarith
  have hBc : ∑ j ∈ Bᶜ, x j ≤ ((R : ℝ) - (B.card : ℝ)) * (s + u) := by
    calc ∑ j ∈ Bᶜ, x j ≤ ∑ _j ∈ Bᶜ, (s + u) := Finset.sum_le_sum fun j _ => hup j
      _ = (Bᶜ.card : ℝ) * (s + u) := by simp; ring
      _ = ((R : ℝ) - (B.card : ℝ)) * (s + u) := by rw [hBc_card]
  have hut : 0 < u + τ := by linarith
  have hkey : (B.card : ℝ) * (u + τ) ≤ u * (R : ℝ) := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hut]
  exact hkey

/-- **Weighted Corank-Share Bound** for a finite family `W` of lattices with positive ranks `d i`
and shifted slopes `x i`: if `u > 0` bounds `x i - s` from above, then the rank-weighted share
with `x i < s - τ` is at most `u / (u + τ)`. -/
theorem weighted_corank_share_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d x : ι → ℝ) (s u τ : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hu : 0 < u) (hτ : 0 ≤ τ)
    (hmean : (∑ i, d i) * s ≤ ∑ i, d i * x i)
    (hup : ∀ i, x i ≤ s + u) :
    ∑ i ∈ Finset.univ.filter (fun i => x i < s - τ), d i ≤ (u / (u + τ)) * (∑ i, d i) := by
  set B := Finset.univ.filter (fun i => x i < s - τ)
  have hsplit : ∑ i, d i * x i = (∑ i ∈ B, d i * x i) + (∑ i ∈ Bᶜ, d i * x i) := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have hB : ∑ i ∈ B, d i * x i ≤ (∑ i ∈ B, d i) * (s - τ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hi).2.le (hd i)
  have hBc_sum : ∑ i ∈ Bᶜ, d i = (∑ i, d i) - ∑ i ∈ B, d i := by
    have : (∑ i ∈ B, d i) + (∑ i ∈ Bᶜ, d i) = ∑ i, d i := by
      rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
    linarith
  have hBc : ∑ i ∈ Bᶜ, d i * x i ≤ ((∑ i, d i) - ∑ i ∈ B, d i) * (s + u) := by
    rw [← hBc_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hup i) (hd i)
  have hut : 0 < u + τ := by linarith
  have hkey : (∑ i ∈ B, d i) * (u + τ) ≤ u * (∑ i, d i) := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hut]
  exact hkey

private lemma indicator_antitone (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) := by
  intro a b hab
  show (if b < c then (1 : ℝ) else 0) ≤ (if a < c then (1 : ℝ) else 0)
  by_cases h1 : b < c
  · have h2 : a < c := lt_of_le_of_lt hab h1
    simp [h1, h2]
  · by_cases h2 : a < c <;> simp [h1, h2]

private lemma indicator_intervalIntegral (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, (if τ < c then (1 : ℝ) else 0) = c := by
  have hi1 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) volume 0 c :=
    (indicator_antitone c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1 : ℝ) else 0) volume c HH :=
    (indicator_antitone c).intervalIntegrable
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by rw [ae_iff]; simp
  have h1 : ∫ τ in (0 : ℝ)..c, (if τ < c then (1 : ℝ) else 0) = ∫ τ in (0 : ℝ)..c, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hc0] at hmem
    simp [lt_of_le_of_ne hmem.2 hx]
  have h2 : ∫ τ in c..HH, (if τ < c then (1 : ℝ) else 0) = ∫ τ in c..HH, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    simp [not_lt.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  simp

private lemma indicator_lower_bound (a xj HH : ℝ) (h : a - HH ≤ xj) (hHH : 0 ≤ HH) :
    a - xj ≤ ∫ τ in (0 : ℝ)..HH, (if τ < a - xj then (1 : ℝ) else 0) := by
  rcases le_total (a - xj) 0 with h0 | h0
  · have hpos : 0 ≤ ∫ τ in (0 : ℝ)..HH, (if τ < a - xj then (1 : ℝ) else 0) :=
      intervalIntegral.integral_nonneg hHH fun _ _ => by split_ifs <;> norm_num
    linarith
  · exact le_of_eq (indicator_intervalIntegral (a - xj) HH h0 (by linarith)).symm

/-- **Layer-Cake Slope Integral Inequality** (`LayerCakeFormula.lean`):
If `x : Fin D → ℝ` (`0 < D`) satisfies `a - HH ≤ x j` for all `j` and the tail count satisfies
`#{j | x j < a - τ} ≤ w τ * D` for all `τ ∈ [0, HH]` with `w` interval integrable on `[0, HH]`,
then `a - ∫ τ in 0..HH, w τ ≤ (∑ j, x j) / D`. -/
theorem layer_cake_slope_integral {D : ℕ} (x : Fin D → ℝ) (a HH : ℝ) (w : ℝ → ℝ)
    (hD : 0 < D) (hHH : 0 ≤ HH) (hx : ∀ j, a - HH ≤ x j)
    (hw : IntervalIntegrable w volume 0 HH)
    (hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) ≤ w τ * (D : ℝ)) :
    a - (∫ τ in (0 : ℝ)..HH, w τ) ≤ (∑ j, x j) / (D : ℝ) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcount : ∀ τ : ℝ, ∑ j : Fin D, (if τ < a - x j then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) := by
    intro τ
    rw [Finset.sum_boole]
    have hf : (Finset.univ.filter fun j : Fin D => τ < a - x j) =
        (Finset.univ.filter fun j : Fin D => x j < a - τ) :=
      Finset.filter_congr fun j _ => by constructor <;> intro hh <;> linarith
    rw [hf]
  have hanti : Antitone (fun τ : ℝ => ∑ j : Fin D, (if τ < a - x j then (1 : ℝ) else 0)) :=
    fun _ _ ht => Finset.sum_le_sum fun j _ => indicator_antitone (a - x j) ht
  have hint : ∫ τ in (0 : ℝ)..HH, ∑ j : Fin D, (if τ < a - x j then (1 : ℝ) else 0) =
      ∑ j : Fin D, ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) :=
    intervalIntegral.integral_finsetSum fun j _ => (indicator_antitone (a - x j)).intervalIntegrable
  have hsum : ∑ j : Fin D, (a - x j) ≤
      ∑ j : Fin D, ∫ τ in (0 : ℝ)..HH, (if τ < a - x j then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => indicator_lower_bound a (x j) HH (hx j) hHH
  have hL : ∑ j : Fin D, (a - x j) = (D : ℝ) * a - ∑ j : Fin D, x j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmono : ∫ τ in (0 : ℝ)..HH, ∑ j : Fin D, (if τ < a - x j then (1 : ℝ) else 0) ≤
      ∫ τ in (0 : ℝ)..HH, (D : ℝ) * w τ := by
    apply intervalIntegral.integral_mono_on hHH hanti.intervalIntegrable (hw.const_mul (D : ℝ))
    intro τ hτ
    rw [hcount τ, mul_comm]
    exact hcnt τ hτ
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [le_div_iff₀ hDpos]
  linarith

/-- **Exact Evaluation of the Bost Corank-Share Integral**:
For `0 < uF` and `0 ≤ HH`,
`∫ τ in 0..HH, 4 * uF / (uF + τ) = 4 * uF * log (1 + HH / uF)`. -/
theorem integral_four_uF_div_add {uF HH : ℝ} (hu : 0 < uF) (hHH : 0 ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, (4 * uF / (uF + τ)) = 4 * uF * Real.log (1 + HH / uF) := by
  have hpos : ∀ τ ∈ Set.uIcc (0 : ℝ) HH, 0 < uF + τ := by
    intro τ hτ
    rw [Set.uIcc_of_le hHH] at hτ
    linarith [hτ.1]
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) HH,
      HasDerivAt (fun t => 4 * uF * Real.log (uF + t)) (4 * uF / (uF + τ)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun t => uF + t) 1 τ := (hasDerivAt_id τ).const_add uF
    have h2 : HasDerivAt (fun t => Real.log (uF + t)) (1 / (uF + τ)) τ := by
      simpa using h1.log (hpos τ hτ).ne'
    rw [← mul_one_div (4 * uF) (uF + τ)]
    exact h2.const_mul (4 * uF)
  have hcont : ContinuousOn (fun τ => 4 * uF / (uF + τ)) (Set.uIcc 0 HH) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) fun τ hτ => (hpos τ hτ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hlog : Real.log (uF + HH) - Real.log (uF + 0) = Real.log (1 + HH / uF) := by
    rw [add_zero, ← Real.log_div (by linarith) hu.ne', add_div, div_self hu.ne']
  rw [← mul_sub, hlog]

/-- Unified tail-density function `(1 - del)⁻¹ * (4 uF / (uF + τ) + η + 4 √e)` handling both
`uF > 0` and the degenerate `uF = 0` case cleanly. -/
def bostTailWeight (del η e uF : ℝ) (τ : ℝ) : ℝ :=
  (1 - del)⁻¹ * ((if uF = 0 then 0 else 4 * uF / (uF + τ)) + (η + 4 * Real.sqrt e))

theorem integral_bostTailWeight {del η e uF HH : ℝ} (hu : 0 ≤ uF) (hHH : 0 ≤ HH) :
    ∫ τ in (0 : ℝ)..HH, bostTailWeight del η e uF τ =
      (1 - del)⁻¹ * (4 * uF * Real.log (1 + HH / uF) + (η + 4 * Real.sqrt e) * HH) := by
  unfold bostTailWeight
  rw [intervalIntegral.integral_const_mul]
  congr 1
  by_cases hu0 : uF = 0
  · subst hu0
    simp only [↓reduceIte, zero_add, mul_zero, div_zero, add_zero, Real.log_one]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  · have hupos : 0 < uF := lt_of_le_of_ne hu (Ne.symm hu0)
    simp only [hu0, ↓reduceIte]
    have hcont : ContinuousOn (fun τ => 4 * uF / (uF + τ)) (Set.uIcc 0 HH) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id) fun τ hτ => by
        rw [Set.uIcc_of_le hHH] at hτ; linarith [hτ.1]
    rw [intervalIntegral.integral_add hcont.intervalIntegrable intervalIntegrable_const,
      integral_four_uF_div_add hupos hHH, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring

theorem intervalIntegrable_bostTailWeight {del η e uF HH : ℝ} (hu : 0 ≤ uF) (hHH : 0 ≤ HH) :
    IntervalIntegrable (bostTailWeight del η e uF) volume 0 HH := by
  unfold bostTailWeight
  apply IntervalIntegrable.const_mul
  by_cases hu0 : uF = 0
  · simp [hu0]
  · have hupos : 0 < uF := lt_of_le_of_ne hu (Ne.symm hu0)
    simp only [hu0, ↓reduceIte]
    have hcont : ContinuousOn (fun τ => 4 * uF / (uF + τ)) (Set.uIcc 0 HH) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id) fun τ hτ => by
        rw [Set.uIcc_of_le hHH] at hτ; linarith [hτ.1]
    exact hcont.intervalIntegrable.add intervalIntegrable_const

/-- **Direct Deduction of `RHDirect.BostSlopeFiber.SlopeIneq` from Harder–Narasimhan Tail Bounds**:
If a `B : RHDirect.BostSlopeFiber` has `0 ≤ B.uF`, `1 ≤ B.cardW`, and its common dual lattice `CC`
has Harder–Narasimhan slopes `x : Fin D → ℝ` (`0 < D`) with average `B.muCC`, lower bound
`∀ j, B.muMinCC ≤ x j`, and tail count bounded by `bostTailWeight B.del B.η B.e B.uF τ * D` for
all `τ ∈ [0, B.HH]`, then **`B.SlopeIneq` holds verbatim**! -/
theorem bostSlopeFiber_slopeIneq_of_tail_bound (B : BostSlopeFiber)
    (D : ℕ) (hD : 0 < D) (x : Fin D → ℝ)
    (hu : 0 ≤ B.uF) (hcard : 1 ≤ B.cardW)
    (havg : (∑ j, x j) / (D : ℝ) = B.muCC)
    (hmin : ∀ j, B.muMinCC ≤ x j)
    (htail : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        ((Finset.univ.filter fun j => x j < B.s - Real.log (B.cardW : ℝ) - τ).card : ℝ)
          ≤ bostTailWeight B.del B.η B.e B.uF τ * (D : ℝ)) :
    B.SlopeIneq := by
  intro hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos
  have hlog_nn : 0 ≤ Real.log (B.cardW : ℝ) := Real.log_nonneg (by exact_mod_cast hcard)
  have hx : ∀ j, (B.s - Real.log (B.cardW : ℝ)) - B.HH ≤ x j := fun j => by
    linarith [hmin j]
  have hlc := layer_cake_slope_integral x (B.s - Real.log (B.cardW : ℝ)) B.HH
    (bostTailWeight B.del B.η B.e B.uF) hD hHH_pos.le hx
    (intervalIntegrable_bostTailWeight hu hHH_pos.le)
    (htail hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos)
  rw [integral_bostTailWeight hu hHH_pos.le, havg] at hlc
  exact hlc

/-- **Frame-to-`BostSlopeFiber.SlopeIneq` Bridge**:
Given an ambient frame space of dimension `D_amb ≤ (1 - B.del)⁻¹ * D` where, for each threshold
`τ ∈ [0, B.HH]`, the Bost slope inequality confines the bad directions `{j | x j < s - log|W| - τ}`
to a subspace of dimension at most `(4 * ε(τ) + B.η + 4 * √B.e) * D_amb` with corank share
`ε(τ) ≤ B.uF / (B.uF + τ)` (from `corank_share_bound` / `weighted_corank_share_bound`),
then **`B.SlopeIneq` holds verbatim**! -/
theorem bostSlopeFiber_slopeIneq_of_corank_frame (B : BostSlopeFiber)
    (D : ℕ) (hD : 0 < D) (x : Fin D → ℝ) (D_amb : ℝ) (ε_share : ℝ → ℝ)
    (hu : 0 < B.uF) (hcard : 1 ≤ B.cardW)
    (havg : (∑ j, x j) / (D : ℝ) = B.muCC)
    (hmin : ∀ j, B.muMinCC ≤ x j)
    (hD_amb_nn : 0 ≤ D_amb)
    (hD_amb_le : B.del < 1 → D_amb ≤ (1 - B.del)⁻¹ * (D : ℝ))
    (hCorank : ∀ τ ∈ Set.Icc (0 : ℝ) B.HH, ε_share τ ≤ B.uF / (B.uF + τ))
    (hFrame : 0 ≤ B.del → B.del < 1 → 0 ≤ B.η → 0 ≤ B.e → B.e ≤ 1 / 4 →
      B.s - B.muMinCC ≤ B.HH → 0 < B.HH →
      ∀ τ ∈ Set.Icc (0 : ℝ) B.HH,
        ((Finset.univ.filter fun j => x j < B.s - Real.log (B.cardW : ℝ) - τ).card : ℝ)
          ≤ (4 * ε_share τ + B.η + 4 * Real.sqrt B.e) * D_amb) :
    B.SlopeIneq := by
  refine bostSlopeFiber_slopeIneq_of_tail_bound B D hD x hu.le hcard havg hmin ?_
  intro hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ
  have h1 := hFrame hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos τ hτ
  have h2 := hCorank τ hτ
  have h3 := hD_amb_le hdel1
  have hpos_coeff : 0 ≤ 4 * (B.uF / (B.uF + τ)) + (B.η + 4 * Real.sqrt B.e) := by
    have : 0 < B.uF + τ := by linarith [hτ.1]
    positivity
  have h4 : (4 * ε_share τ + B.η + 4 * Real.sqrt B.e) * D_amb ≤
      (4 * (B.uF / (B.uF + τ)) + (B.η + 4 * Real.sqrt B.e)) * ((1 - B.del)⁻¹ * (D : ℝ)) := by
    calc (4 * ε_share τ + B.η + 4 * Real.sqrt B.e) * D_amb
        ≤ (4 * (B.uF / (B.uF + τ)) + (B.η + 4 * Real.sqrt B.e)) * D_amb :=
          mul_le_mul_of_nonneg_right (by linarith) hD_amb_nn
      _ ≤ (4 * (B.uF / (B.uF + τ)) + (B.η + 4 * Real.sqrt B.e)) * ((1 - B.del)⁻¹ * (D : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 hpos_coeff
  have hEq : (4 * (B.uF / (B.uF + τ)) + (B.η + 4 * Real.sqrt B.e)) * ((1 - B.del)⁻¹ * (D : ℝ)) =
      bostTailWeight B.del B.η B.e B.uF τ * (D : ℝ) := by
    unfold bostTailWeight
    simp only [hu.ne', ↓reduceIte]
    ring
  linarith

end LayerCakeAndBostFiber

/-! ## Section 5: Archimedean Covolume vs. Non-Archimedean Divisibility Comparison on Fibers -/

section FiberComparison

/-- **Bost Fiber Covolume-vs-Divisibility Comparison**:
Combines `B.SlopeIneq` with a non-archimedean divisibility upper bound `B.muCC ≤ divUpper`
to produce the sharp ceiling on the weighted mean slope `B.s`. -/
theorem bostSlopeFiber_covolume_comparison (B : BostSlopeFiber) (divUpper : ℝ)
    (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η) (he0 : 0 ≤ B.e) (he4 : B.e ≤ 1 / 4)
    (hHH_ge : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hDiv : B.muCC ≤ divUpper) :
    B.s ≤ divUpper + Real.log (B.cardW : ℝ) +
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH) := by
  have h := hSlope hdel0 hdel1 hη he0 he4 hHH_ge hHH_pos
  linarith

/-- **Sharp Rank-Share Bound & Vanishing Criterion on a `BostSlopeFiber`**:
Suppose `B.s = (∑ u, d u * score u) / (∑ u, d u)` is the rank-weighted mean over a family `W`
(with `d u > 0`), `B.SlopeIneq` holds alongside `B.muCC ≤ divUpper`, every exceptional member
`u ∈ Exc` has `score u ≥ gain`, and every non-exceptional member `u ∉ Exc` has `score u ≥ base`
(with `base < gain`). Then the exceptional rank share satisfies:
`(∑_{u ∈ Exc} d u) / (∑_u d u) ≤ (divUpper + loss(B) - base) / (gain - base)`. -/
theorem bostSlopeFiber_exceptional_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BostSlopeFiber) (d score : ι → ℝ) (Exc : Finset ι) (divUpper gain base : ℝ)
    (hd : ∀ u, 0 < d u) (hDpos : 0 < ∑ u, d u)
    (hmean : B.s = (∑ u, d u * score u) / (∑ u, d u))
    (hSlope : B.SlopeIneq)
    (hdel0 : 0 ≤ B.del) (hdel1 : B.del < 1) (hη : 0 ≤ B.η) (he0 : 0 ≤ B.e) (he4 : B.e ≤ 1 / 4)
    (hHH_ge : B.s - B.muMinCC ≤ B.HH) (hHH_pos : 0 < B.HH)
    (hDiv : B.muCC ≤ divUpper)
    (hExc : ∀ u ∈ Exc, gain ≤ score u)
    (hRest : ∀ u ∉ Exc, base ≤ score u)
    (hGap : base < gain) :
    (∑ u ∈ Exc, d u) / (∑ u, d u) ≤
      (divUpper + Real.log (B.cardW : ℝ) +
        (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
          (B.η + 4 * Real.sqrt B.e) * B.HH) - base) / (gain - base) := by
  have hS := bostSlopeFiber_covolume_comparison B divUpper hSlope hdel0 hdel1 hη he0 he4
    hHH_ge hHH_pos hDiv
  have hsplit : ∑ u, d u * score u = (∑ u ∈ Exc, d u * score u) + (∑ u ∈ Excᶜ, d u * score u) := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have h1 : (∑ u ∈ Exc, d u) * gain ≤ ∑ u ∈ Exc, d u * score u := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hExc u hu) (hd u).le
  have h2 : (∑ u ∈ Excᶜ, d u) * base ≤ ∑ u ∈ Excᶜ, d u * score u := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u hu =>
      mul_le_mul_of_nonneg_left (hRest u (Finset.mem_compl.mp hu)) (hd u).le
  have htot : (∑ u ∈ Exc, d u) + (∑ u ∈ Excᶜ, d u) = ∑ u, d u := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have h3_alg : (∑ u ∈ Exc, d u) * (gain - base) + (∑ u, d u) * base =
      (∑ u ∈ Exc, d u) * gain + (∑ u ∈ Excᶜ, d u) * base := by
    rw [← htot]; ring
  have h3 : (∑ u ∈ Exc, d u) * (gain - base) + (∑ u, d u) * base ≤ ∑ u, d u * score u := by
    linarith
  have h4 : ∑ u, d u * score u ≤ (∑ u, d u) * (divUpper + Real.log (B.cardW : ℝ) +
      (1 - B.del)⁻¹ * (4 * B.uF * Real.log (1 + B.HH / B.uF) +
        (B.η + 4 * Real.sqrt B.e) * B.HH)) := by
    rw [hmean, div_le_iff₀ hDpos] at hS
    linarith
  have hgap_pos : 0 < gain - base := sub_pos.mpr hGap
  rw [div_le_div_iff₀ hDpos hgap_pos]
  nlinarith

end FiberComparison

end

end RHDirect.ArakelovCovolume
