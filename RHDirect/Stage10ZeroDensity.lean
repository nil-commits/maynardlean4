import RHDirect.Stage5ZetaZeroFree
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# RHDirect.Stage10ZeroDensity

Unconditional (0-assumption, 0-`sorry`, 0-custom-`axiom`) Stage 10 analytic number theory in pure
Mathlib `v4.33.1`, establishing:

1. **Unconditional Montgomery–Vaughan Hilbert Inequality**:
   - Sharp `Real.pi` Hilbert inequality for arbitrary `δ`-well-spaced real frequencies
     (`montgomery_vaughan_hilbert_inequality`), proved via the spectral theorem for Hermitian
     matrices, the Montgomery–Vaughan eigenvector partial-fraction cancellation identity, and
     Euler's `∑ 1 / n² = π² / 6`.
   - Logarithmic weighted Hilbert inequality (`hilbert_inequality_log`) for `λ_n = Real.log n`,
     proved via exact-divisor finite subdivision into uniformly spaced frequencies plus symmetric
     pairing and Schur's test (`w_k = k^(-1/2)`).
2. **Unconditional Mean-Value Theorem & Discrete Large Sieve for Dirichlet Polynomials**:
   - Exact off-diagonal mean-value bound (`dirichletPoly_mean_value_exact_bound`),
     upper bound (`dirichletPoly_mean_value_upper`), and asymptotic mean square
     (`dirichletPoly_mean_value_tendsto`).
   - Sobolev–Gallagher pointwise inequality (`sobolev_gallagher_pointwise`) and unconditional
     discrete large-sieve mean-value theorem (`dirichletPoly_discrete_large_sieve`) for
     arbitrary `δ`-well-spaced vertical points `t_r ∈ [-T, T]`.
3. **Unconditional Second Moment of `riemannZeta` on `Re(s) > 1/2`** (Section 3).
4. **Unconditional Large-Sieve Zero-Detecting Bound** (Section 4).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Real Matrix

namespace RHDirect.Stage10ZeroDensity

/-! ## Section 1: Unconditional Montgomery–Vaughan Hilbert Inequality -/

/-- Auxiliary bound on the sum of inverse squared distances from one point in a `δ`-well-spaced
finite set of reals to all other points: `∑ r ≠ s, 1 / (λ r - λ s)^2 ≤ (π^2 / 3) / δ^2`. -/
lemma sum_inv_sq_dist_le_pi_sq_div_three {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|)
    {s : ι} (hs : s ∈ S) :
    ∑ r ∈ S.erase s, (1 : ℝ) / (lam r - lam s) ^ 2 ≤ (Real.pi ^ 2 / 3) / δ ^ 2 := by
  have hzeta : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have htsum : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  -- Helper: for any subset `A ⊆ S.erase s` and real map `φ` preserving `δ`-separation with `φ s < φ r`
  have hside : ∀ (A : Finset ι) (φ : ι → ℝ),
      A ⊆ S.erase s →
      (∀ r ∈ S, ∀ t ∈ S, r ≠ t → δ ≤ |φ r - φ t|) →
      (∀ r ∈ A, φ s < φ r) →
      ∑ r ∈ A, (1 : ℝ) / (φ r - φ s) ^ 2 ≤ (Real.pi ^ 2 / 6) / δ ^ 2 := by
    intro A φ hAS hφsep hgt
    have hinj : Set.InjOn φ A := by
      intro x hx y hy hxy
      by_contra hne
      have hxS : x ∈ S := Finset.mem_of_mem_erase (hAS hx)
      have hyS : y ∈ S := Finset.mem_of_mem_erase (hAS hy)
      have h1 := hφsep x hxS y hyS hne
      rw [hxy, sub_self, abs_zero] at h1
      linarith
    set B : Finset ℝ := A.image φ
    have hsum_eq : ∑ r ∈ A, (1 : ℝ) / (φ r - φ s) ^ 2 =
        ∑ x ∈ B, (1 : ℝ) / (x - φ s) ^ 2 :=
      (Finset.sum_image (f := fun x : ℝ => (1 : ℝ) / (x - φ s) ^ 2) hinj).symm
    rw [hsum_eq]
    set emb : Fin B.card ↪o ℝ := B.orderEmbOfFin rfl
    have hsum_fin : ∑ x ∈ B, (1 : ℝ) / (x - φ s) ^ 2 =
        ∑ i : Fin B.card, (1 : ℝ) / (emb i - φ s) ^ 2 := by
      have hrange : Finset.univ.map emb.toEmbedding = B := by
        ext x
        simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
        have hr := Finset.range_orderEmbOfFin B rfl
        change x ∈ Set.range emb ↔ x ∈ (B : Set ℝ)
        rw [hr]
      conv_lhs => rw [← hrange]
      rw [Finset.sum_map]
      rfl
    rw [hsum_fin]
    have hmemB : ∀ i : Fin B.card, emb i ∈ B := fun i => Finset.orderEmbOfFin_mem B rfl i
    have hstep : ∀ i : Fin B.card, ((i : ℕ) + 1 : ℝ) * δ ≤ emb i - φ s := by
      intro ⟨k, hk⟩
      induction k with
      | zero =>
        obtain ⟨r, hrA, hrEq⟩ := Finset.mem_image.mp (hmemB ⟨0, hk⟩)
        have hrS : r ∈ S := Finset.mem_of_mem_erase (hAS hrA)
        have hrne : r ≠ s := (Finset.mem_erase.mp (hAS hrA)).1
        have hpos : 0 < φ r - φ s := sub_pos.mpr (hgt r hrA)
        have h1 := hφsep r hrS s hs hrne
        rw [abs_of_pos hpos] at h1
        simpa [hrEq] using h1
      | succ k ih =>
        have hk' : k < B.card := Nat.lt_of_succ_lt hk
        have hih := ih hk'
        obtain ⟨r₁, hr₁A, hr₁Eq⟩ := Finset.mem_image.mp (hmemB ⟨k, hk'⟩)
        obtain ⟨r₂, hr₂A, hr₂Eq⟩ := Finset.mem_image.mp (hmemB ⟨k + 1, hk⟩)
        have hlt : emb ⟨k, hk'⟩ < emb ⟨k + 1, hk⟩ := emb.strictMono (by show k < k + 1; omega)
        have hrne : r₂ ≠ r₁ := by
          intro h; rw [h, hr₁Eq] at hr₂Eq; exact hlt.ne hr₂Eq
        have hsep12 := hφsep r₂ (Finset.mem_of_mem_erase (hAS hr₂A))
          r₁ (Finset.mem_of_mem_erase (hAS hr₁A)) hrne
        rw [hr₁Eq, hr₂Eq, abs_of_pos (sub_pos.mpr hlt)] at hsep12
        push_cast
        linarith
    have hle1 : ∑ i : Fin B.card, (1 : ℝ) / (emb i - φ s) ^ 2 ≤
        ∑ i : Fin B.card, (1 : ℝ) / (((i : ℕ) + 1 : ℝ) * δ) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi_pos : (0 : ℝ) < ((i : ℕ) + 1 : ℝ) * δ := by positivity
      have hgi := hstep i
      exact one_div_le_one_div_of_le (sq_pos_of_pos hi_pos) (sq_le_sq' (by linarith) hgi)
    have hle2 : ∑ i : Fin B.card, (1 : ℝ) / (((i : ℕ) + 1 : ℝ) * δ) ^ 2 =
        (1 / δ ^ 2) * ∑ k ∈ Finset.range B.card, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.sum_fin_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [dif_pos (Finset.mem_range.mp hk)]
      push_cast; field_simp [hδ.ne']
    have hle3 : ∑ k ∈ Finset.range B.card, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤
        Real.pi ^ 2 / 6 := by
      rw [← htsum]
      have hsub : ∑ k ∈ Finset.range B.card, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 =
          ∑ n ∈ Finset.Icc 1 B.card, (1 : ℝ) / (n : ℝ) ^ 2 := by
        refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
        · intro a _ b _ h; omega
        · intro n hn; rw [Finset.mem_Icc] at hn; exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro k _; rfl
      rw [hsub]
      exact hzeta.sum_le_tsum (Finset.Icc 1 B.card) (fun n _ => by positivity)
    calc ∑ i : Fin B.card, (1 : ℝ) / (emb i - φ s) ^ 2
        ≤ (1 / δ ^ 2) * ∑ k ∈ Finset.range B.card, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
          linarith [hle1, hle2]
      _ ≤ (1 / δ ^ 2) * (Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left hle3 (by positivity)
      _ = (Real.pi ^ 2 / 6) / δ ^ 2 := by ring
  set Rset := (S.erase s).filter (fun r => lam s < lam r)
  set Lset := (S.erase s).filter (fun r => lam r < lam s)
  have hpart : S.erase s = Rset ∪ Lset := by
    ext r
    simp only [Rset, Lset, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hr
      have hrne : r ≠ s := (Finset.mem_erase.mp hr).1
      have hrS : r ∈ S := Finset.mem_of_mem_erase hr
      have hne : lam r ≠ lam s := by
        intro h
        have h1 := hsep r hrS s hs hrne
        rw [h, sub_self, abs_zero] at h1
        linarith
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr ⟨hr, hlt⟩
      · exact Or.inl ⟨hr, hgt⟩
    · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
  have hdisj : Disjoint Rset Lset := by
    rw [Finset.disjoint_left]
    intro r hrR hrL
    simp only [Rset, Lset, Finset.mem_filter] at hrR hrL
    linarith [hrR.2, hrL.2]
  have hR : ∑ r ∈ Rset, (1 : ℝ) / (lam r - lam s) ^ 2 ≤ (Real.pi ^ 2 / 6) / δ ^ 2 :=
    hside Rset lam (Finset.filter_subset _ _) hsep (fun r hr => (Finset.mem_filter.mp hr).2)
  have hL : ∑ r ∈ Lset, (1 : ℝ) / (lam r - lam s) ^ 2 ≤ (Real.pi ^ 2 / 6) / δ ^ 2 := by
    have hsep_neg : ∀ r ∈ S, ∀ t ∈ S, r ≠ t → δ ≤ |(-lam r) - (-lam t)| := by
      intro r hr t ht hrt
      rw [show (-lam r) - (-lam t) = -(lam r - lam t) by ring, abs_neg]
      exact hsep r hr t ht hrt
    have heq : ∑ r ∈ Lset, (1 : ℝ) / (lam r - lam s) ^ 2 =
        ∑ r ∈ Lset, (1 : ℝ) / ((-lam r) - (-lam s)) ^ 2 :=
      Finset.sum_congr rfl fun r _ => by congr 1; ring
    rw [heq]
    exact hside Lset (fun r => -lam r) (Finset.filter_subset _ _) hsep_neg
      (fun r hr => neg_lt_neg (Finset.mem_filter.mp hr).2)
  rw [hpart, Finset.sum_union hdisj]
  have halg : (Real.pi ^ 2 / 6) / δ ^ 2 + (Real.pi ^ 2 / 6) / δ ^ 2 = (Real.pi ^ 2 / 3) / δ ^ 2 := by ring
  linarith

/-- **Unconditional Sharp Montgomery–Vaughan Hilbert Inequality** (constant `Real.pi`):
for any finite set `S`, real frequencies `lam : ι → ℝ` with uniform spacing `δ > 0`
(`∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|`), and any complex coefficients `a : ι → ℂ`,
`‖∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ)‖ ≤ (Real.pi / δ) * ∑ r ∈ S, ‖a r‖ ^ 2`. -/
theorem montgomery_vaughan_hilbert_inequality {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|)
    (a : ι → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ)‖ ≤
      (Real.pi / δ) * ∑ r ∈ S, ‖a r‖ ^ 2 := by
  let α := {x : ι // x ∈ S}
  have hdiff_ne : ∀ r s : α, r ≠ s → ((lam r.1 - lam s.1 : ℝ) : ℂ) ≠ 0 := by
    intro r s hrs
    have hne : r.1 ≠ s.1 := fun h => hrs (Subtype.ext h)
    have h1 := hsep r.1 r.2 s.1 s.2 hne
    exact Complex.ofReal_ne_zero.mpr (by intro h; rw [h, abs_zero] at h1; linarith)
  let A : Matrix α α ℂ := fun r s =>
    if r = s then 0 else Complex.I / ((lam r.1 - lam s.1 : ℝ) : ℂ)
  have hA : A.IsHermitian := by
    ext r s
    rw [Matrix.conjTranspose_apply]
    dsimp only [A]
    by_cases h : r = s
    · subst h; simp
    · have h' : s ≠ r := Ne.symm h
      rw [if_neg h', if_neg h]
      simp only [star_div₀, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      have hsub : ((lam s.1 - lam r.1 : ℝ) : ℂ) = -((lam r.1 - lam s.1 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsub, div_neg, neg_div, neg_neg]
  -- Step 1: Every eigenvalue `μ` of `A` satisfies `|μ| ≤ Real.pi / δ`.
  have heig_bound : ∀ j : α, |hA.eigenvalues j| ≤ Real.pi / δ := by
    intro j
    set μ : ℝ := hA.eigenvalues j
    set u : α → ℂ := ⇑(hA.eigenvectorBasis j)
    have hu_norm : ∑ r : α, ‖u r‖ ^ 2 = 1 := by
      have h1 := hA.eigenvectorBasis.orthonormal.1 j
      have h2 : ‖hA.eigenvectorBasis j‖ ^ 2 = ∑ r : α, ‖u r‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      rw [← h2, h1, one_pow]
    have heig_eq : ∀ r : α,
        ∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ) =
          -Complex.I * (μ : ℂ) * u r := by
      intro r
      have hmv := congrFun (hA.mulVec_eigenvectorBasis j) r
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul, A] at hmv
      have hsum : ∑ s : α, (if r = s then 0 else Complex.I / ((lam r.1 - lam s.1 : ℝ) : ℂ)) * u s =
          Complex.I * ∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), if_pos rfl, zero_mul, zero_add,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hne : r ≠ s := (Finset.mem_erase.mp hs).1.symm
        rw [if_neg hne]; ring
      rw [hsum] at hmv
      have hmul := congrArg (fun z : ℂ => -Complex.I * z) hmv
      have hI : -Complex.I * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      calc ∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)
          = (-Complex.I * Complex.I) * ∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ) := by
            rw [hI, one_mul]
        _ = -Complex.I * (Complex.I * ∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)) := by
            ring
        _ = -Complex.I * ((μ : ℂ) * u r) := hmul
        _ = -Complex.I * (μ : ℂ) * u r := by ring
    have heig_conj : ∀ r : α,
        ∑ s ∈ Finset.univ.erase r, star (u s) / ((lam r.1 - lam s.1 : ℝ) : ℂ) =
          Complex.I * (μ : ℂ) * star (u r) := by
      intro r
      have h := congrArg (starRingEnd ℂ) (heig_eq r)
      simp only [map_sum, map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
        neg_neg] at h
      simpa only [Complex.star_def] using h
    have hmu_sq_C : ((μ ^ 2 : ℝ) : ℂ) =
        ∑ r : α, (∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)) *
          (∑ t ∈ Finset.univ.erase r, star (u t) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) := by
      have hterm : ∀ r : α,
          (∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)) *
            (∑ t ∈ Finset.univ.erase r, star (u t) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            ((μ ^ 2 : ℝ) : ℂ) * ((‖u r‖ ^ 2 : ℝ) : ℂ) := by
        intro r
        rw [heig_eq r, heig_conj r]
        have hnorm : u r * star (u r) = ((‖u r‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        calc (-Complex.I * (μ : ℂ) * u r) * (Complex.I * (μ : ℂ) * star (u r))
            = (-Complex.I * Complex.I) * ((μ : ℂ) ^ 2) * (u r * star (u r)) := by ring
          _ = 1 * ((μ : ℂ) ^ 2) * ((‖u r‖ ^ 2 : ℝ) : ℂ) := by
            rw [neg_mul, Complex.I_mul_I, neg_neg, hnorm]
          _ = ((μ ^ 2 : ℝ) : ℂ) * ((‖u r‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      simp_rw [hterm, ← Finset.mul_sum]
      have hsum_one : ∑ r : α, ((‖u r‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_sum, hu_norm, Complex.ofReal_one]
      rw [hsum_one, mul_one]
    have hexpand :
        ∑ r : α, (∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)) *
          (∑ t ∈ Finset.univ.erase r, star (u t) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
        (∑ s : α, ((‖u s‖ ^ 2 : ℝ) : ℂ) *
            ∑ r ∈ Finset.univ.erase s, (1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2) +
        (∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (u s * star (u t)) *
              ∑ r ∈ (Finset.univ.erase s).erase t,
                (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ))) := by
      have h1 : ∀ r : α,
          (∑ s ∈ Finset.univ.erase r, u s / ((lam r.1 - lam s.1 : ℝ) : ℂ)) *
            (∑ t ∈ Finset.univ.erase r, star (u t) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
          ∑ s ∈ Finset.univ.erase r, ∑ t ∈ Finset.univ.erase r,
            (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) := by
        intro r
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      simp_rw [h1]
      have h2 : ∀ r : α, ∀ s ∈ Finset.univ.erase r,
          ∑ t ∈ Finset.univ.erase r,
              (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            ((‖u s‖ ^ 2 : ℝ) : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2 +
            ∑ t ∈ (Finset.univ.erase r).erase s,
              (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) := by
        intro r s hs
        rw [← Finset.add_sum_erase _ _ hs]
        congr 1
        have hnorm : u s * star (u s) = ((‖u s‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hnorm, ← pow_two ((lam r.1 - lam s.1 : ℝ) : ℂ)]
      have h3 : ∑ r : α, ∑ s ∈ Finset.univ.erase r, ∑ t ∈ Finset.univ.erase r,
            (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
          (∑ r : α, ∑ s ∈ Finset.univ.erase r,
            ((‖u s‖ ^ 2 : ℝ) : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2) +
          (∑ r : α, ∑ s ∈ Finset.univ.erase r, ∑ t ∈ (Finset.univ.erase r).erase s,
            (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s hs => h2 r s hs
      rw [h3]
      congr 1
      · have hswap1 : ∑ r : α, ∑ s ∈ Finset.univ.erase r,
              ((‖u s‖ ^ 2 : ℝ) : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2 =
            ∑ r : α, ∑ s : α,
              if s = r then 0 else ((‖u s‖ ^ 2 : ℝ) : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), if_pos rfl, zero_add]
          exact Finset.sum_congr rfl fun s hs => (if_neg (Finset.mem_erase.mp hs).1).symm
        rw [hswap1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), if_pos rfl, zero_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [if_neg (Finset.mem_erase.mp hr).1.symm]
        ring
      · let F : α → α → α → ℂ := fun r s t =>
          if s = r ∨ t = r ∨ t = s then 0
          else (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ))
        have hL : ∑ r : α, ∑ s ∈ Finset.univ.erase r, ∑ t ∈ (Finset.univ.erase r).erase s,
              (u s * star (u t)) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            ∑ r : α, ∑ s : α, ∑ t : α, F r s t := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
          have hzero1 : ∑ t : α, F r r t = 0 := Finset.sum_eq_zero fun t _ => by simp [F]
          rw [hzero1, zero_add]
          refine Finset.sum_congr rfl fun s hs => ?_
          have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
          have hzero2 : F r s r = 0 := by simp [F]
          rw [hzero2, zero_add]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hsr, Finset.mem_univ s⟩)]
          have hzero3 : F r s s = 0 := by simp [F]
          rw [hzero3, zero_add]
          refine Finset.sum_congr rfl fun t ht => ?_
          have hts : t ≠ s := (Finset.mem_erase.mp ht).1
          have htr : t ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
          simp [F, hsr, htr, hts]
        have hR : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              (u s * star (u t)) *
                ∑ r ∈ (Finset.univ.erase s).erase t,
                  (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            ∑ s : α, ∑ t : α, ∑ r : α, F r s t := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
          have hzero1 : ∑ r : α, F r s s = 0 := Finset.sum_eq_zero fun r _ => by simp [F]
          rw [hzero1, zero_add]
          refine Finset.sum_congr rfl fun t ht => ?_
          have hts : t ≠ s := (Finset.mem_erase.mp ht).1
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
          have hzero2 : F s s t = 0 := by simp [F]
          rw [hzero2, zero_add]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)]
          have hzero3 : F t s t = 0 := by simp [F]
          rw [hzero3, zero_add, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
          have hrs : r ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
          simp only [F, hrs.symm, hrt.symm, hts, or_self, ↓reduceIte]
          ring
        rw [hL, hR]
        calc ∑ r : α, ∑ s : α, ∑ t : α, F r s t
            = ∑ s : α, ∑ r : α, ∑ t : α, F r s t := Finset.sum_comm
          _ = ∑ s : α, ∑ t : α, ∑ r : α, F r s t :=
              Finset.sum_congr rfl fun s _ => Finset.sum_comm
    let B : α → ℂ := fun s => ∑ r ∈ Finset.univ.erase s, (1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ)
    have hoff_pf : ∀ s : α, ∀ t ∈ Finset.univ.erase s,
        ∑ r ∈ (Finset.univ.erase s).erase t,
            (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
          ((1 : ℂ) / ((lam s.1 - lam t.1 : ℝ) : ℂ)) *
            (B s - B t + 2 / ((lam s.1 - lam t.1 : ℝ) : ℂ)) := by
      intro s t ht
      have hts : t ≠ s := (Finset.mem_erase.mp ht).1
      have hst : s ≠ t := hts.symm
      have hdst : ((lam s.1 - lam t.1 : ℝ) : ℂ) ≠ 0 := hdiff_ne s t hst
      have hpf : ∀ r ∈ (Finset.univ.erase s).erase t,
          (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            ((1 : ℂ) / ((lam s.1 - lam t.1 : ℝ) : ℂ)) *
              ((1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) - (1 : ℂ) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) := by
        intro r hr
        have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
        have hrs : r ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
        have hdrs := hdiff_ne r s hrs
        have hdrt := hdiff_ne r t hrt
        field_simp [hdst, hdrs, hdrt]
        push_cast; ring
      rw [Finset.sum_congr rfl hpf, ← Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      have hBs : ∑ r ∈ (Finset.univ.erase s).erase t, (1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) =
          B s - (1 : ℂ) / ((lam t.1 - lam s.1 : ℝ) : ℂ) := by
        have h := Finset.add_sum_erase (Finset.univ.erase s)
          (fun r => (1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ)) ht
        dsimp only [B]; linear_combination h
      have hBt : ∑ r ∈ (Finset.univ.erase s).erase t, (1 : ℂ) / ((lam r.1 - lam t.1 : ℝ) : ℂ) =
          B t - (1 : ℂ) / ((lam s.1 - lam t.1 : ℝ) : ℂ) := by
        have hset : (Finset.univ.erase s).erase t = (Finset.univ.erase t).erase s :=
          Finset.erase_right_comm
        rw [hset]
        have hs_mem : s ∈ Finset.univ.erase t := Finset.mem_erase.mpr ⟨hst, Finset.mem_univ s⟩
        have h := Finset.add_sum_erase (Finset.univ.erase t)
          (fun r => (1 : ℂ) / ((lam r.1 - lam t.1 : ℝ) : ℂ)) hs_mem
        dsimp only [B]; linear_combination h
      rw [hBs, hBt]
      have hneg : ((lam t.1 - lam s.1 : ℝ) : ℂ) = -((lam s.1 - lam t.1 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hneg]; field_simp [hdst]; ring
    have hoff_eq :
        ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (u s * star (u t)) *
              ∑ r ∈ (Finset.univ.erase s).erase t,
                (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
        2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (u s * star (u t)) / ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2 := by
      have hrew : ∀ s : α, ∀ t ∈ Finset.univ.erase s,
          (u s * star (u t)) *
              ∑ r ∈ (Finset.univ.erase s).erase t,
                (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
            (B s * u s * (star (u t) / ((lam s.1 - lam t.1 : ℝ) : ℂ))) -
            (B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ))) +
            2 * ((u s * star (u t)) / ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2) := by
        intro s t ht
        rw [hoff_pf s t ht]
        ring
      have hsplit :
          ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              (u s * star (u t)) *
                ∑ r ∈ (Finset.univ.erase s).erase t,
                  (1 : ℂ) / (((lam r.1 - lam s.1 : ℝ) : ℂ) * ((lam r.1 - lam t.1 : ℝ) : ℂ)) =
          (∑ s : α, ∑ t ∈ Finset.univ.erase s,
              B s * u s * (star (u t) / ((lam s.1 - lam t.1 : ℝ) : ℂ))) -
          (∑ s : α, ∑ t ∈ Finset.univ.erase s,
              B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ))) +
          2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              (u s * star (u t)) / ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2 := by
        have h2mul : 2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              (u s * star (u t)) / ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2 =
            ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              2 * ((u s * star (u t)) / ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => Finset.mul_sum _ _ _
        rw [h2mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t ht => hrew s t ht
      rw [hsplit]
      have hP1 : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            B s * u s * (star (u t) / ((lam s.1 - lam t.1 : ℝ) : ℂ)) =
          Complex.I * (μ : ℂ) * ∑ s : α, B s * (u s * star (u s)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.mul_sum, heig_conj s]
        ring
      have hP2 : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ)) =
          Complex.I * (μ : ℂ) * ∑ t : α, B t * (u t * star (u t)) := by
        have hswap : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ)) =
            ∑ t : α, ∑ s ∈ Finset.univ.erase t,
              B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ)) := by
          have hL : ∀ s : α, ∑ t ∈ Finset.univ.erase s,
                B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ)) =
              ∑ t : α, if t = s then 0 else B t * star (u t) * (u s / ((lam s.1 - lam t.1 : ℝ) : ℂ)) := by
            intro s
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), if_pos rfl, zero_add]
            exact Finset.sum_congr rfl fun t ht => (if_neg (Finset.mem_erase.mp ht).1).symm
          simp_rw [hL]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), if_pos rfl, zero_add]
          exact Finset.sum_congr rfl fun s hs => if_neg (Finset.mem_erase.mp hs).1.symm
        rw [hswap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.mul_sum]
        have hneg_sum : ∑ s ∈ Finset.univ.erase t, u s / ((lam s.1 - lam t.1 : ℝ) : ℂ) =
            -(∑ s ∈ Finset.univ.erase t, u s / ((lam t.1 - lam s.1 : ℝ) : ℂ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          have hsub : ((lam s.1 - lam t.1 : ℝ) : ℂ) = -((lam t.1 - lam s.1 : ℝ) : ℂ) := by
            push_cast; ring
          rw [hsub, div_neg]
        rw [hneg_sum, heig_eq t]
        ring
      rw [hP1, hP2, sub_self, zero_add]
    have hmu_sq_R : μ ^ 2 =
        (∑ s : α, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2) +
        2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (u s * star (u t)).re / (lam s.1 - lam t.1) ^ 2 := by
      have hre := congrArg Complex.re (hmu_sq_C.trans (hexpand.trans (by rw [hoff_eq])))
      simp only [Complex.ofReal_re, Complex.add_re, Complex.re_sum, Complex.mul_re,
        Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
      rw [hre]
      congr 1
      · refine Finset.sum_congr rfl fun s _ => ?_
        have h1 : ∀ r : α, (((1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2)).re =
            (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 := by
          intro r
          rw [show (1 : ℂ) / ((lam r.1 - lam s.1 : ℝ) : ℂ) ^ 2 =
            (((1 : ℝ) / (lam r.1 - lam s.1) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
        simp only [Complex.ofReal_im, zero_mul, sub_zero, h1]
      · congr 1
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [show ((lam s.1 - lam t.1 : ℝ) : ℂ) ^ 2 = (((lam s.1 - lam t.1) ^ 2 : ℝ) : ℂ) by
          push_cast; ring, Complex.div_ofReal_re]
    have hoff_le : 2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
          (u s * star (u t)).re / (lam s.1 - lam t.1) ^ 2 ≤
        2 * ∑ s : α, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 := by
      have h1 : 2 * ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (u s * star (u t)).re / (lam s.1 - lam t.1) ^ 2 ≤
          ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / (lam s.1 - lam t.1) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun t _ => ?_
        have hden : 0 ≤ (lam s.1 - lam t.1) ^ 2 := sq_nonneg _
        have hre_le : 2 * (u s * star (u t)).re ≤ ‖u s‖ ^ 2 + ‖u t‖ ^ 2 := by
          have hcs : (u s * star (u t)).re ≤ ‖u s‖ * ‖u t‖ := by
            calc (u s * star (u t)).re ≤ ‖u s * star (u t)‖ := Complex.re_le_norm _
              _ = ‖u s‖ * ‖u t‖ := by rw [norm_mul, norm_star]
          nlinarith [sq_nonneg (‖u s‖ - ‖u t‖)]
        calc 2 * ((u s * star (u t)).re / (lam s.1 - lam t.1) ^ 2)
            = (2 * (u s * star (u t)).re) / (lam s.1 - lam t.1) ^ 2 := by ring
          _ ≤ (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / (lam s.1 - lam t.1) ^ 2 :=
              div_le_div_of_nonneg_right hre_le hden
      have h2 : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
            (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / (lam s.1 - lam t.1) ^ 2 =
          2 * ∑ s : α, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 := by
        have hsplit : ∑ s : α, ∑ t ∈ Finset.univ.erase s,
              (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / (lam s.1 - lam t.1) ^ 2 =
            (∑ s : α, ∑ t ∈ Finset.univ.erase s, ‖u s‖ ^ 2 / (lam s.1 - lam t.1) ^ 2) +
            (∑ s : α, ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 / (lam s.1 - lam t.1) ^ 2) := by
          simp_rw [add_div, Finset.sum_add_distrib]
        rw [hsplit]
        have hA1 : ∑ s : α, ∑ t ∈ Finset.univ.erase s, ‖u s‖ ^ 2 / (lam s.1 - lam t.1) ^ 2 =
            ∑ s : α, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have : (lam s.1 - lam r.1) ^ 2 = (lam r.1 - lam s.1) ^ 2 := by ring
          rw [this]; ring
        have hA2 : ∑ s : α, ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 / (lam s.1 - lam t.1) ^ 2 =
            ∑ t : α, ‖u t‖ ^ 2 * ∑ r ∈ Finset.univ.erase t, (1 : ℝ) / (lam r.1 - lam t.1) ^ 2 := by
          have hL : ∀ s : α, ∑ t ∈ Finset.univ.erase s, ‖u t‖ ^ 2 / (lam s.1 - lam t.1) ^ 2 =
              ∑ t : α, if t = s then 0 else ‖u t‖ ^ 2 / (lam s.1 - lam t.1) ^ 2 := by
            intro s
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), if_pos rfl, zero_add]
            exact Finset.sum_congr rfl fun t ht => (if_neg (Finset.mem_erase.mp ht).1).symm
          simp_rw [hL]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), if_pos rfl, zero_add, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [if_neg (Finset.mem_erase.mp hr).1.symm]
          ring
        rw [hA1, hA2]; ring
      linarith
    have hdist_bd : ∀ s : α,
        ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 ≤
          (Real.pi ^ 2 / 3) / δ ^ 2 := by
      intro s
      have heq : ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 =
          ∑ r ∈ S.erase s.1, (1 : ℝ) / (lam r - lam s.1) ^ 2 := by
        refine Finset.sum_bij (fun r _ => r.1) ?_ ?_ ?_ ?_
        · intro r hr
          exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hr).1 (Subtype.ext h), r.2⟩
        · intro r₁ _ r₂ _ h; exact Subtype.ext h
        · intro r hr
          have hrS := Finset.mem_of_mem_erase hr
          have hrne := (Finset.mem_erase.mp hr).1
          exact ⟨⟨r, hrS⟩, Finset.mem_erase.mpr ⟨fun h => hrne (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
        · intro _ _; rfl
      rw [heq]
      exact sum_inv_sq_dist_le_pi_sq_div_three S lam hδ hsep s.2
    have hmu_sq_le : μ ^ 2 ≤ (Real.pi / δ) ^ 2 := by
      calc μ ^ 2
          ≤ 3 * ∑ s : α, ‖u s‖ ^ 2 * ∑ r ∈ Finset.univ.erase s, (1 : ℝ) / (lam r.1 - lam s.1) ^ 2 := by
            linarith [hmu_sq_R, hoff_le]
        _ ≤ 3 * ∑ s : α, ‖u s‖ ^ 2 * ((Real.pi ^ 2 / 3) / δ ^ 2) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) (by positivity)
            exact mul_le_mul_of_nonneg_left (hdist_bd s) (sq_nonneg _)
        _ = 3 * ((∑ s : α, ‖u s‖ ^ 2) * ((Real.pi ^ 2 / 3) / δ ^ 2)) := by
            rw [← Finset.sum_mul]
        _ = (Real.pi / δ) ^ 2 := by rw [hu_norm, one_mul]; ring
    have hpos : 0 ≤ Real.pi / δ := by positivity
    nlinarith [sq_abs μ, abs_nonneg μ]
  -- Step 2: Expand `v r := star (a r.1)` in the orthonormal eigenbasis `hA.eigenvectorBasis`!
  let v : EuclideanSpace ℂ α := WithLp.toLp 2 (fun r : α => star (a r.1))
  have hv_norm : ‖v‖ ^ 2 = ∑ r ∈ S, ‖a r‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h1 : ∑ r : α, ‖v r‖ ^ 2 = ∑ r : α, ‖a r.1‖ ^ 2 := by
      refine Finset.sum_congr rfl fun r _ => ?_
      change ‖star (a r.1)‖ ^ 2 = ‖a r.1‖ ^ 2
      rw [norm_star]
    rw [h1]
    exact Finset.sum_coe_sort S (fun r => ‖a r‖ ^ 2)
  have hAv_eq : dotProduct (star ⇑v) (A *ᵥ ⇑v) =
      Complex.I * ∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, A]
    have h1 : ∑ r : α, star (v r) * ∑ s : α,
          (if r = s then 0 else Complex.I / ((lam r.1 - lam s.1 : ℝ) : ℂ)) * v s =
        Complex.I * ∑ r : α, ∑ s ∈ Finset.univ.erase r,
          a r.1 * star (a s.1) / ((lam r.1 - lam s.1 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), if_pos rfl, zero_mul, zero_add,
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hne : r ≠ s := (Finset.mem_erase.mp hs).1.symm
      rw [if_neg hne]
      have hvr : star (v r) = a r.1 := by change star (star (a r.1)) = a r.1; exact star_star _
      have hvs : v s = star (a s.1) := rfl
      rw [hvr, hvs]; ring
    change ∑ r : α, star (v r) * ∑ s : α,
        (if r = s then 0 else Complex.I / ((lam r.1 - lam s.1 : ℝ) : ℂ)) * v s = _
    rw [h1]
    congr 1
    calc ∑ r : α, ∑ s ∈ Finset.univ.erase r, a r.1 * star (a s.1) / ((lam r.1 - lam s.1 : ℝ) : ℂ)
        = ∑ r : α, ∑ s ∈ S.erase r.1, a r.1 * star (a s) / ((lam r.1 - lam s : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          refine Finset.sum_bij (fun s _ => s.1) ?_ ?_ ?_ ?_
          · intro s hs
            exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hs).1 (Subtype.ext h), s.2⟩
          · intro s₁ _ s₂ _ h; exact Subtype.ext h
          · intro s hs
            have hsS := Finset.mem_of_mem_erase hs
            have hsne := (Finset.mem_erase.mp hs).1
            exact ⟨⟨s, hsS⟩, Finset.mem_erase.mpr ⟨fun h => hsne (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
          · intro _ _; rfl
      _ = ∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ) :=
          Finset.sum_coe_sort S (fun r => ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ))
  set c : α → ℂ := fun j => @inner ℂ (EuclideanSpace ℂ α) _ (hA.eigenvectorBasis j) v
  have hv_repr : v = ∑ j : α, c j • hA.eigenvectorBasis j :=
    (hA.eigenvectorBasis.sum_repr' v).symm
  have hc_parseval : ∑ j : α, ‖c j‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := hA.eigenvectorBasis.repr.norm_map v
    rw [← h, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hA.eigenvectorBasis.repr_apply_apply v j]
  have hAv_repr : A *ᵥ ⇑v = ⇑(∑ j : α, ((hA.eigenvalues j : ℂ) * c j) • hA.eigenvectorBasis j) := by
    have hv_coe : ⇑v = ∑ j : α, c j • ⇑(hA.eigenvectorBasis j) := by
      ext r; conv_lhs => rw [hv_repr]
      simp
    rw [hv_coe, Matrix.mulVec_sum]
    ext r
    simp only [Finset.sum_apply]
    rw [show (⇑(∑ j : α, ((hA.eigenvalues j : ℂ) * c j) • hA.eigenvectorBasis j)) r =
        ∑ j : α, ((hA.eigenvalues j : ℂ) * c j) * (hA.eigenvectorBasis j) r by
      simp [Finset.sum_apply]]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis j]
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  have hquad : dotProduct (star ⇑v) (A *ᵥ ⇑v) = ∑ j : α, (hA.eigenvalues j : ℂ) * ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
    have hinner : dotProduct (star ⇑v) (A *ᵥ ⇑v) =
        @inner ℂ (EuclideanSpace ℂ α) _ v (∑ j : α, ((hA.eigenvalues j : ℂ) * c j) • hA.eigenvectorBasis j) := by
      rw [hAv_repr, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [hinner, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    have hcj : @inner ℂ (EuclideanSpace ℂ α) _ v (hA.eigenvectorBasis j) = star (c j) := by
      rw [← inner_conj_symm]
      rfl
    rw [hcj]
    have hnorm : c j * star (c j) = ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc (hA.eigenvalues j : ℂ) * c j * star (c j)
        = (hA.eigenvalues j : ℂ) * (c j * star (c j)) := by ring
      _ = (hA.eigenvalues j : ℂ) * ((‖c j‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
  calc ‖∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ)‖
      = ‖Complex.I * ∑ r ∈ S, ∑ s ∈ S.erase r, a r * star (a s) / ((lam r - lam s : ℝ) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖∑ j : α, (hA.eigenvalues j : ℂ) * ((‖c j‖ ^ 2 : ℝ) : ℂ)‖ := by rw [← hAv_eq, hquad]
    _ ≤ ∑ j : α, ‖(hA.eigenvalues j : ℂ) * ((‖c j‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ j : α, |hA.eigenvalues j| * ‖c j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
          Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ ∑ j : α, (Real.pi / δ) * ‖c j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (heig_bound j) (sq_nonneg _)
    _ = (Real.pi / δ) * ∑ r ∈ S, ‖a r‖ ^ 2 := by
        rw [← Finset.mul_sum, hc_parseval, hv_norm]

/-- Elementary cube-reciprocal bound: `∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ)^3 ≤ 2`. -/
lemma sum_inv_cube_le_two (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ^ 3 ≤ 2 := by
  have htel : ∀ k : ℕ, 2 ≤ k → (1 : ℝ) / (k : ℝ) ^ 3 ≤ (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have h1 : (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
      field_simp [hkm1.ne', hk0.ne']; ring
    rw [h1]
    have hle : ((k : ℝ) - 1) * (k : ℝ) ≤ (k : ℝ) ^ 3 := by
      have : (k : ℝ) ^ 3 - ((k : ℝ) - 1) * (k : ℝ) = (k : ℝ) * ((k : ℝ) ^ 2 - (k : ℝ) + 1) := by ring
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) hle
  cases N with
  | zero => simp
  | succ m =>
    have hsplit : ∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ) ^ 3 =
        1 + ∑ k ∈ Finset.Icc 2 (m + 1), (1 : ℝ) / (k : ℝ) ^ 3 := by
      have h1 : Finset.Icc 1 (m + 1) = insert 1 (Finset.Icc 2 (m + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      norm_num
    have hsum_le : ∑ k ∈ Finset.Icc 2 (m + 1), (1 : ℝ) / (k : ℝ) ^ 3 ≤
        ∑ k ∈ Finset.Icc 2 (m + 1), ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) :=
      Finset.sum_le_sum fun k hk => htel k (Finset.mem_Icc.mp hk).1
    have htel_val : ∀ r : ℕ,
        ∑ k ∈ Finset.Icc 2 (r + 1), ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) =
          1 - (1 : ℝ) / ((r + 1 : ℕ) : ℝ) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        have hIcc : Finset.Icc 2 (r + 2) = insert (r + 2) (Finset.Icc 2 (r + 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        push_cast; ring
    have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
    linarith [htel_val m]

/-- Elementary log lower bound for integer ratios: for `1 ≤ n < m`,
`(m - n : ℝ) / (m : ℝ) ≤ Real.log ((m : ℝ) / (n : ℝ))`. -/
lemma sub_div_le_log_div {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    ((m : ℝ) - (n : ℝ)) / (m : ℝ) ≤ Real.log ((m : ℝ) / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hn0)
  have h2 : 1 - ((m : ℝ) / (n : ℝ))⁻¹ = ((m : ℝ) - (n : ℝ)) / (m : ℝ) := by
    field_simp [hn0.ne', hm0.ne']
  linarith

/-- Elementary log spacing lower bound: for `1 ≤ n < m`,
`1 / (2 * (n : ℝ)) ≤ Real.log (m : ℝ) - Real.log (n : ℝ)`. -/
lemma inv_two_mul_le_log_sub_log {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    (1 : ℝ) / (2 * (n : ℝ)) ≤ Real.log (m : ℝ) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnp1 : (n + 1 : ℕ) ≤ m := hnm
  have hlog_mono : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hnp1)
  have h1 : ((n + 1 : ℕ) - (n : ℝ)) / ((n + 1 : ℕ) : ℝ) ≤
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
    sub_div_le_log_div hn (Nat.lt_succ_self n)
  rw [Real.log_div (by positivity) hn0.ne'] at h1
  have h2 : (1 : ℝ) / (2 * (n : ℝ)) ≤ ((n + 1 : ℕ) - (n : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast
    rw [show (n : ℝ) + 1 - (n : ℝ) = 1 by ring]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **Unconditional Logarithmic Montgomery–Vaughan Hilbert Inequality (`hilbert_inequality_log`)**:
for every `N : ℕ` and `a : ℕ → ℂ`,
`‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, a m * star (a n) / Real.log ((m : ℝ) / n)‖ ≤ (4 * Real.pi + 5) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2`.

Proved completely algebraically with zero integrals or limits via exact-divisor subdivision into
uniformly spaced frequencies, sharp `montgomery_vaughan_hilbert_inequality`, symmetric offset
pairing, and Schur's test (`w_k = k^(-1/2)`). -/
theorem hilbert_inequality_log (N : ℕ) (a : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        a m * star (a n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)‖ ≤
      (4 * Real.pi + 5) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by
  by_cases hN : N = 0
  · subst hN; simp
  have hNpos : 1 ≤ N := Nat.pos_of_ne_zero hN
  set M : ℕ := Nat.factorial N
  have hMpos : 0 < M := Nat.factorial_pos N
  have hMposR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  let kn : ℕ → ℕ := fun n => M / n
  have hkn_mul : ∀ n ∈ Finset.Icc 1 N, kn n * n = M := by
    intro n hn
    have hndvd : n ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    exact Nat.div_mul_cancel hndvd
  have hkn_pos : ∀ n ∈ Finset.Icc 1 N, 0 < kn n := by
    intro n hn
    have hmul := hkn_mul n hn
    by_contra h0
    push Not at h0
    have : kn n = 0 := Nat.eq_zero_of_le_zero h0
    rw [this, zero_mul] at hmul
    omega
  let P : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc 1 N).sigma (fun n => Finset.range (kn n))
  let δ : ℝ := 1 / (4 * (M : ℝ))
  have hδ : 0 < δ := by positivity
  let offset : ℕ → ℕ → ℝ := fun n j => (2 * (j : ℝ) + 1 - (kn n : ℝ)) / (8 * (M : ℝ))
  let lam : (Σ _ : ℕ, ℕ) → ℝ := fun p => Real.log (p.1 : ℝ) + offset p.1 p.2
  let b : (Σ _ : ℕ, ℕ) → ℂ := fun p => a p.1 / (kn p.1 : ℂ)
  have hoffset_le : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.range (kn n),
      |offset n j| ≤ ((kn n : ℝ) - 1) / (8 * (M : ℝ)) := by
    intro n hn j hj
    have hjlt : j < kn n := Finset.mem_range.mp hj
    have hjR : (j : ℝ) ≤ (kn n : ℝ) - 1 := by
      have : j + 1 ≤ kn n := hjlt
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ (kn n : ℝ) := Nat.cast_le.mpr this
      push_cast at hcast; linarith
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    dsimp only [offset]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * (M : ℝ))]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [abs_le]
    constructor <;> linarith
  have hoffset_lt : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.range (kn n),
      |offset n j| < 1 / (8 * (n : ℝ)) := by
    intro n hn j hj
    have h1 := hoffset_le n hn j hj
    have hmulR : (kn n : ℝ) * (n : ℝ) = (M : ℝ) := by exact_mod_cast hkn_mul n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
    have h2 : ((kn n : ℝ) - 1) / (8 * (M : ℝ)) < (kn n : ℝ) / (8 * (M : ℝ)) := by
      apply div_lt_div_of_pos_right _ (by positivity); linarith
    have h3 : (kn n : ℝ) / (8 * (M : ℝ)) = 1 / (8 * (n : ℝ)) := by
      rw [← hmulR]; field_simp [hn0.ne', (show (kn n : ℝ) ≠ 0 by exact_mod_cast (hkn_pos n hn).ne')]
    linarith
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ |lam p - lam q| := by
    intro p hp q hq hpq
    simp only [P, Finset.mem_sigma, Finset.mem_range] at hp hq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := by
        intro h2'
        apply hpq
        cases p; cases q
        simp only at h1 h2'
        subst h1; subst h2'; rfl
      have hdiff : lam p - lam q = ((p.2 : ℝ) - (q.2 : ℝ)) / (4 * (M : ℝ)) := by
        dsimp only [lam, offset]; rw [h1]; ring
      rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (M : ℝ))]
      have hge1 : (1 : ℝ) ≤ |(p.2 : ℝ) - (q.2 : ℝ)| := by
        rcases lt_or_gt_of_ne h2 with hlt | hgt
        · have hcast : ((p.2 + 1 : ℕ) : ℝ) ≤ (q.2 : ℝ) := Nat.cast_le.mpr hlt
          push_cast at hcast; rw [abs_of_neg (by linarith)]; linarith
        · have hcast : ((q.2 + 1 : ℕ) : ℝ) ≤ (p.2 : ℝ) := Nat.cast_le.mpr hgt
          push_cast at hcast; rw [abs_of_pos (by linarith)]; linarith
      exact div_le_div_of_nonneg_right hge1 (by positivity)
    · have hsym : ∀ {n m : ℕ} {jn jm : ℕ}, n ∈ Finset.Icc 1 N → m ∈ Finset.Icc 1 N →
          n < m → jn < kn n → jm < kn m → δ ≤ lam ⟨m, jm⟩ - lam ⟨n, jn⟩ := by
        intro n m jn jm hn hm hnm hjn hjm
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
        have hlog := inv_two_mul_le_log_sub_log hn1 hnm
        have hon := (abs_lt.mp (hoffset_lt n hn jn (Finset.mem_range.mpr hjn))).2
        have hom := (abs_lt.mp (hoffset_lt m hm jm (Finset.mem_range.mpr hjm))).1
        have hnmR : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
        have h18 : 1 / (8 * (m : ℝ)) ≤ 1 / (8 * (n : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have hnM : (n : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr
          (Nat.le_of_dvd hMpos (Nat.dvd_factorial hn1 (Finset.mem_Icc.mp hn).2))
        have hδn : δ ≤ 1 / (4 * (n : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have hgap : 1 / (2 * (n : ℝ)) - 1 / (8 * (n : ℝ)) - 1 / (8 * (n : ℝ)) = 1 / (4 * (n : ℝ)) := by ring
        dsimp only [lam]
        linarith
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have hpos := hsym hp.1 hq.1 hlt hp.2 hq.2
        have : lam p - lam q = -(lam ⟨q.1, q.2⟩ - lam ⟨p.1, p.2⟩) := by ring
        rw [this, abs_neg, abs_of_pos (lt_of_lt_of_le hδ hpos)]
        exact hpos
      · have hpos := hsym hq.1 hp.1 hgt hq.2 hp.2
        have : lam p - lam q = lam ⟨p.1, p.2⟩ - lam ⟨q.1, q.2⟩ := rfl
        rw [this, abs_of_pos (lt_of_lt_of_le hδ hpos)]
        exact hpos
  -- Step 1: Apply sharp `montgomery_vaughan_hilbert_inequality` to `(P, lam, δ, b)`
  have hMV := montgomery_vaughan_hilbert_inequality P lam hδ hsep b
  have hRHS_eq : (Real.pi / δ) * ∑ p ∈ P, ‖b p‖ ^ 2 =
      4 * Real.pi * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by
    dsimp only [P]
    rw [Finset.sum_sigma]
    have hinner : ∀ n ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.range (kn n), ‖b ⟨n, j⟩‖ ^ 2 = ((n : ℝ) / (M : ℝ)) * ‖a n‖ ^ 2 := by
      intro n hn
      have hkn0 : (kn n : ℝ) ≠ 0 := by exact_mod_cast (hkn_pos n hn).ne'
      have hmulR : (kn n : ℝ) * (n : ℝ) = (M : ℝ) := by exact_mod_cast hkn_mul n hn
      simp only [b, norm_div, Complex.norm_natCast, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hkn0, hMposR.ne']
      rw [← hmulR]; ring
    rw [Finset.sum_congr rfl hinner]
    dsimp only [δ]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp [hMposR.ne']
  -- Step 2: Expand LHS double sum over `P × P` into same-block (= 0) + cross-block
  have hLHS_expand :
      ∑ p ∈ P, ∑ q ∈ P.erase p, b p * star (b q) / ((lam p - lam q : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        a m * star (a n) *
          (((1 : ℂ) / ((kn m : ℂ) * (kn n : ℂ))) *
            ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
              (1 : ℂ) / ((lam ⟨m, j⟩ - lam ⟨n, k⟩ : ℝ) : ℂ)) := by
    have h1 : ∑ p ∈ P, ∑ q ∈ P.erase p, b p * star (b q) / ((lam p - lam q : ℝ) : ℂ) =
        ∑ p ∈ P, ∑ q ∈ P, if p = q then 0 else b p * star (b q) / ((lam p - lam q : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.add_sum_erase _ _ hp, if_pos rfl, zero_add]
      exact Finset.sum_congr rfl fun q hq => (if_neg (Finset.mem_erase.mp hq).1.symm).symm
    rw [h1]
    dsimp only [P]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp_rw [Finset.sum_sigma]
    rw [Finset.sum_comm]
    rw [← Finset.add_sum_erase _ _ hm]
    have hdiag_zero : ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn m),
          (if (⟨m, j⟩ : Σ _ : ℕ, ℕ) = ⟨m, k⟩ then (0 : ℂ) else
            b ⟨m, j⟩ * star (b ⟨m, k⟩) / ((lam ⟨m, j⟩ - lam ⟨m, k⟩ : ℝ) : ℂ)) = 0 := by
      set S0 := ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn m),
          (if (⟨m, j⟩ : Σ _ : ℕ, ℕ) = ⟨m, k⟩ then (0 : ℂ) else
            b ⟨m, j⟩ * star (b ⟨m, k⟩) / ((lam ⟨m, j⟩ - lam ⟨m, k⟩ : ℝ) : ℂ))
      have hneg : S0 = -S0 := by
        dsimp only [S0]
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hjk : j = k
        · subst hjk; simp
        · have h1' : (⟨m, j⟩ : Σ _ : ℕ, ℕ) ≠ ⟨m, k⟩ := fun h => hjk (by cases h; rfl)
          have h2' : (⟨m, k⟩ : Σ _ : ℕ, ℕ) ≠ ⟨m, j⟩ := fun h => hjk (by cases h; rfl)
          rw [if_neg h1', if_neg h2']
          have hsub : ((lam ⟨m, j⟩ - lam ⟨m, k⟩ : ℝ) : ℂ) = -((lam ⟨m, k⟩ - lam ⟨m, j⟩ : ℝ) : ℂ) := by
            push_cast; ring
          rw [hsub, div_neg]
      have h2S0 : (2 : ℂ) * S0 = 0 := by linear_combination hneg
      exact (mul_eq_zero.mp h2S0).resolve_left two_ne_zero
    rw [hdiag_zero, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : (⟨m, j⟩ : Σ _ : ℕ, ℕ) ≠ ⟨n, k⟩ := fun h => hnm (congrArg Sigma.fst h).symm
    rw [if_neg hne]
    simp only [b, star_div₀, Complex.star_def, Complex.conj_natCast]
    ring
  -- Step 3: Error kernel `E m n` + symmetric pairing bound
  let E : ℕ → ℕ → ℝ := fun m n =>
    (1 / ((kn m : ℝ) * (kn n : ℝ))) *
      ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
        (1 / (lam ⟨m, j⟩ - lam ⟨n, k⟩) - 1 / Real.log ((m : ℝ) / (n : ℝ)))
  have hdiff_eq :
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          a m * star (a n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)) =
      (∑ p ∈ P, ∑ q ∈ P.erase p, b p * star (b q) / ((lam p - lam q : ℝ) : ℂ)) -
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          a m * star (a n) * ((E m n : ℝ) : ℂ)) := by
    rw [hLHS_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnI := Finset.mem_of_mem_erase hn
    have hkm0 : (kn m : ℂ) ≠ 0 := by exact_mod_cast (hkn_pos m hm).ne'
    have hkn0 : (kn n : ℂ) ≠ 0 := by exact_mod_cast (hkn_pos n hnI).ne'
    have hE_cast : ((E m n : ℝ) : ℂ) =
        ((1 : ℂ) / ((kn m : ℂ) * (kn n : ℂ))) *
          ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
            (1 : ℂ) / ((lam ⟨m, j⟩ - lam ⟨n, k⟩ : ℝ) : ℂ) -
        (1 : ℂ) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ) := by
      dsimp only [E]
      push_cast
      simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hkm0, hkn0]
    rw [hE_cast]; ring
  have hE_bound : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N, n < m →
      |E m n| ≤ (1 / 12) / ((n : ℝ) ^ 2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) := by
    intro m hm n hn hnm
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hnmR : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
    set Δ : ℝ := Real.log ((m : ℝ) / (n : ℝ))
    have hΔ_eq : Δ = Real.log (m : ℝ) - Real.log (n : ℝ) := Real.log_div hm0.ne' hn0.ne'
    have hΔ_ge : 1 / (2 * (n : ℝ)) ≤ Δ := by rw [hΔ_eq]; exact inv_two_mul_le_log_sub_log hn1 hnm
    have hΔ_pos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ_ge
    let g : ℕ → ℕ → ℝ := fun j k => 1 / (lam ⟨m, j⟩ - lam ⟨n, k⟩) - 1 / Δ
    have hinv_off : ∀ {r : ℕ} {j : ℕ}, j < kn r →
        offset r (kn r - 1 - j) = -offset r j := by
      intro r j hj
      dsimp only [offset]
      have hcast : ((kn r - 1 - j : ℕ) : ℝ) = (kn r : ℝ) - 1 - (j : ℝ) := by
        have h2 : (kn r - 1 - j) + (j + 1) = kn r := by omega
        have h3 : (((kn r - 1 - j) + (j + 1) : ℕ) : ℝ) = (kn r : ℝ) := Nat.cast_inj.mpr h2
        push_cast at h3; linarith
      rw [hcast]; ring
    have hsum_sym : ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n), g j k =
        ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
          g (kn m - 1 - j) (kn n - 1 - k) := by
      have hbij : ∀ (L : ℕ) (f : ℕ → ℝ),
          ∑ j ∈ Finset.range L, f j = ∑ j ∈ Finset.range L, f (L - 1 - j) := by
        intro L f
        refine Finset.sum_bij (fun j _ => L - 1 - j) ?_ ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
        · intro a ha b hb h; rw [Finset.mem_range] at ha hb; omega
        · intro j hj; rw [Finset.mem_range] at hj
          exact ⟨L - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j hj; rw [Finset.mem_range] at hj; congr 1; omega
      rw [hbij (kn m)]
      refine Finset.sum_congr rfl fun j _ => hbij (kn n) _
    have havg : E m n = (1 / ((kn m : ℝ) * (kn n : ℝ))) *
        ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
          ((g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2) := by
      dsimp only [E]
      have h1 : ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
            ((g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2) =
          (∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n), g j k +
           ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n), g (kn m - 1 - j) (kn n - 1 - k)) / 2 := by
        simp_rw [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [h1, ← hsum_sym]
      ring
    have hterm_le : ∀ j ∈ Finset.range (kn m), ∀ k ∈ Finset.range (kn n),
        |(g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2| ≤
          (1 / 12) / ((n : ℝ) ^ 2 * Δ ^ 3) := by
      intro j hj k hk
      set w : ℝ := offset m j - offset n k
      have hw_le : |w| ≤ 1 / (4 * (n : ℝ)) := by
        have h1 := hoffset_lt m hm j hj
        have h2 := hoffset_lt n hn k hk
        have h18 : 1 / (8 * (m : ℝ)) ≤ 1 / (8 * (n : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        calc |offset m j - offset n k|
            ≤ |offset m j| + |offset n k| := abs_sub _ _
          _ ≤ 1 / (8 * (m : ℝ)) + 1 / (8 * (n : ℝ)) := by linarith
          _ ≤ 1 / (8 * (n : ℝ)) + 1 / (8 * (n : ℝ)) := by linarith
          _ = 1 / (4 * (n : ℝ)) := by ring
      have hw_half : |w| ≤ Δ / 2 := by
        have hhalf : (1 / (2 * (n : ℝ))) / 2 = 1 / (4 * (n : ℝ)) := by ring
        linarith
      have hΔw_pos : 0 < Δ + w := by linarith [(abs_le.mp hw_half).1]
      have hΔmw_pos : 0 < Δ - w := by linarith [(abs_le.mp hw_half).2]
      have hlam1 : lam ⟨m, j⟩ - lam ⟨n, k⟩ = Δ + w := by
        dsimp only [lam, w]; linarith [hΔ_eq]
      have hlam2 : lam ⟨m, kn m - 1 - j⟩ - lam ⟨n, kn n - 1 - k⟩ = Δ - w := by
        dsimp only [lam]
        rw [hinv_off (Finset.mem_range.mp hj), hinv_off (Finset.mem_range.mp hk)]
        dsimp only [w]; linarith [hΔ_eq]
      have halg : (g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2 =
          w ^ 2 / (Δ * (Δ ^ 2 - w ^ 2)) := by
        dsimp only [g]
        rw [hlam1, hlam2]
        have hden : Δ ^ 2 - w ^ 2 ≠ 0 := by nlinarith [hΔw_pos, hΔmw_pos]
        field_simp [hΔ_pos.ne', hΔw_pos.ne', hΔmw_pos.ne', hden]
        ring
      rw [halg]
      have hden_ge : (3 / 4) * Δ ^ 2 ≤ Δ ^ 2 - w ^ 2 := by
        have hw2 : w ^ 2 ≤ (Δ / 2) ^ 2 := by
          rw [← sq_abs w]; exact sq_le_sq' (by linarith [abs_nonneg w]) hw_half
        linarith
      have hden_pos : 0 < Δ * (Δ ^ 2 - w ^ 2) :=
        mul_pos hΔ_pos (by linarith [sq_pos_of_pos hΔ_pos])
      rw [abs_of_nonneg (div_nonneg (sq_nonneg w) hden_pos.le)]
      have hw2_n : w ^ 2 ≤ 1 / (16 * (n : ℝ) ^ 2) := by
        have h1 : w ^ 2 ≤ (1 / (4 * (n : ℝ))) ^ 2 := by
          rw [← sq_abs w]; exact sq_le_sq' (by linarith [abs_nonneg w]) hw_le
        linarith [show (1 / (4 * (n : ℝ))) ^ 2 = 1 / (16 * (n : ℝ) ^ 2) by ring]
      calc w ^ 2 / (Δ * (Δ ^ 2 - w ^ 2))
          ≤ (1 / (16 * (n : ℝ) ^ 2)) / (Δ * ((3 / 4) * Δ ^ 2)) :=
            div_le_div₀ (by positivity) hw2_n (by positivity)
              (mul_le_mul_of_nonneg_left hden_ge hΔ_pos.le)
        _ = (1 / 12) / ((n : ℝ) ^ 2 * Δ ^ 3) := by ring
    rw [havg, abs_mul, abs_of_pos (by
      have := hkn_pos m hm; have := hkn_pos n hn; positivity)]
    calc (1 / ((kn m : ℝ) * (kn n : ℝ))) *
          |∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
              ((g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2)|
        ≤ (1 / ((kn m : ℝ) * (kn n : ℝ))) *
          ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
            |(g j k + g (kn m - 1 - j) (kn n - 1 - k)) / 2| := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (1 / ((kn m : ℝ) * (kn n : ℝ))) *
          ∑ j ∈ Finset.range (kn m), ∑ k ∈ Finset.range (kn n),
            ((1 / 12) / ((n : ℝ) ^ 2 * Δ ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm_le j hj k hk
      _ = (1 / 12) / ((n : ℝ) ^ 2 * Δ ^ 3) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hkm0 : (kn m : ℝ) ≠ 0 := by exact_mod_cast (hkn_pos m hm).ne'
          have hkn0 : (kn n : ℝ) ≠ 0 := by exact_mod_cast (hkn_pos n hn).ne'
          field_simp [hkm0, hkn0]
  have hE_antisymm : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → E n m = -E m n := by
    intro m n hm hn
    have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    dsimp only [E]
    rw [Finset.sum_comm]
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hn0.ne' hm0.ne', Real.log_div hm0.ne' hn0.ne']; ring
    have hneg : ∀ j k : ℕ,
        1 / (lam ⟨n, k⟩ - lam ⟨m, j⟩) - 1 / Real.log ((n : ℝ) / (m : ℝ)) =
        -(1 / (lam ⟨m, j⟩ - lam ⟨n, k⟩) - 1 / Real.log ((m : ℝ) / (n : ℝ))) := by
      intro j k
      rw [hlog, show lam ⟨n, k⟩ - lam ⟨m, j⟩ = -(lam ⟨m, j⟩ - lam ⟨n, k⟩) by ring, div_neg, div_neg]
      ring
    simp_rw [hneg, Finset.sum_neg_distrib]
    ring
  -- Step 4: Schur's test on the error sum with weight `w_k = k^(-1/2)`
  let K : ℕ → ℕ → ℝ := fun m n =>
    (1 / 12) / (Real.sqrt (m : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
  have hrow_sum : ∀ n ∈ Finset.Icc 1 N,
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => n < m),
        K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)) ≤ 3 / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsimp : ∀ m ∈ (Finset.Icc 1 N).filter (fun m => n < m),
        K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)) =
        (1 / 12) * (1 / (n : ℝ) ^ 2) * (1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)) := by
      intro m hm
      have hnm : n < m := (Finset.mem_filter.mp hm).2
      have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hn52 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
        norm_num
      dsimp only [K]
      rw [hn52]
      have hsq_n_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      have hsq_m_ne : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
      field_simp [hsq_n_ne, hsq_m_ne]
      rw [Real.sq_sqrt hm0.le]
    rw [Finset.sum_congr rfl hsimp, ← Finset.mul_sum]
    set S1 := ((Finset.Icc 1 N).filter (fun m => n < m)).filter (fun m => m ≤ 2 * n)
    set S2 := ((Finset.Icc 1 N).filter (fun m => n < m)).filter (fun m => 2 * n < m)
    have hpart : (Finset.Icc 1 N).filter (fun m => n < m) = S1 ∪ S2 := by
      ext m; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; by_cases h2 : m ≤ 2 * n
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, by omega⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro m h1 h2
      simp only [S1, S2, Finset.mem_filter] at h1 h2; omega
    rw [hpart, Finset.sum_union hdisj]
    have hS1 : (1 / (n : ℝ) ^ 2) * ∑ m ∈ S1, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤ 16 := by
      have hle : ∑ m ∈ S1, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤
          ∑ m ∈ S1, 8 * (n : ℝ) ^ 2 / ((m : ℝ) - (n : ℝ)) ^ 3 := by
        refine Finset.sum_le_sum fun m hm => ?_
        simp only [S1, Finset.mem_filter] at hm
        have hnm : n < m := hm.1.2
        have hm2n : (m : ℝ) ≤ 2 * (n : ℝ) := by
          have hcast : (m : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_le.mpr hm.2
          push_cast at hcast; linarith
        have hmn_pos : 0 < (m : ℝ) - (n : ℝ) := by
          have hlt : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
          linarith
        have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
        have hlog_ge : ((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) ≤ Real.log ((m : ℝ) / (n : ℝ)) := by
          have h1 := sub_div_le_log_div hn1 hnm
          have h2 : ((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ)) ≤ ((m : ℝ) - (n : ℝ)) / (m : ℝ) :=
            div_le_div_of_nonneg_left hmn_pos.le hm0 hm2n
          linarith
        have hlog_cub : (((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ))) ^ 3 ≤ (Real.log ((m : ℝ) / (n : ℝ))) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hlog_ge 3
        have hden : (n : ℝ) * (((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ))) ^ 3 ≤
            (m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3 :=
          mul_le_mul (Nat.cast_le.mpr hnm.le) hlog_cub (by positivity) hm0.le
        calc 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
            ≤ 1 / ((n : ℝ) * (((m : ℝ) - (n : ℝ)) / (2 * (n : ℝ))) ^ 3) :=
              one_div_le_one_div_of_le (by positivity) hden
          _ = 8 * (n : ℝ) ^ 2 / ((m : ℝ) - (n : ℝ)) ^ 3 := by
              field_simp [hn0.ne', hmn_pos.ne']; ring
      calc (1 / (n : ℝ) ^ 2) * ∑ m ∈ S1, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
          ≤ (1 / (n : ℝ) ^ 2) * ∑ m ∈ S1, 8 * (n : ℝ) ^ 2 / ((m : ℝ) - (n : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 8 * ∑ m ∈ S1, (1 : ℝ) / ((m : ℝ) - (n : ℝ)) ^ 3 := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            field_simp [hn0.ne']
        _ ≤ 8 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 3 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hinj : ∑ m ∈ S1, (1 : ℝ) / ((m : ℝ) - (n : ℝ)) ^ 3 =
                ∑ k ∈ S1.image (fun m => m - n), (1 : ℝ) / (k : ℝ) ^ 3 := by
              rw [Finset.sum_image]
              · refine Finset.sum_congr rfl fun m hm => ?_
                have hnm : n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
                rw [Nat.cast_sub hnm.le]
              · intro a ha b hb hab
                dsimp only at hab
                have ha' : n < a := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
                have hb' : n < b := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
                omega
            rw [hinj]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro k hk
            obtain ⟨m, hmS1, rfl⟩ := Finset.mem_image.mp hk
            simp only [S1, Finset.mem_filter] at hmS1
            rw [Finset.mem_Icc]; omega
        _ ≤ 8 * 2 := mul_le_mul_of_nonneg_left (sum_inv_cube_le_two n) (by positivity)
        _ = 16 := by norm_num
    have hS2 : (1 / (n : ℝ) ^ 2) * ∑ m ∈ S2, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤ 2 := by
      have htel : ∀ m : ℕ, 2 * n < m →
          1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤
            1 / (2 * (Real.log (((m - 1 : ℕ) : ℝ) / (n : ℝ))) ^ 2) -
            1 / (2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 2) := by
        intro m hm
        have hm1 : 2 * n ≤ m - 1 := by omega
        have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
        have hmm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        set a1 : ℝ := Real.log (((m - 1 : ℕ) : ℝ) / (n : ℝ))
        set a2 : ℝ := Real.log ((m : ℝ) / (n : ℝ))
        have ha1_pos : 0 < a1 := Real.log_pos (by
          rw [one_lt_div hn0]
          have hcast : ((2 * n : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hm1
          push_cast at hcast; linarith)
        have ha12 : a1 ≤ a2 := Real.log_le_log (div_pos hmm1_pos hn0)
          (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le m 1)) hn0.le)
        have ha2_pos : 0 < a2 := lt_of_lt_of_le ha1_pos ha12
        have hdiff_ge : 1 / (m : ℝ) ≤ a2 - a1 := by
          have h1 : a2 - a1 = Real.log ((m : ℝ) / ((m - 1 : ℕ) : ℝ)) := by
            dsimp only [a1, a2]
            rw [Real.log_div hm0.ne' hn0.ne', Real.log_div hmm1_pos.ne' hn0.ne',
              Real.log_div hm0.ne' hmm1_pos.ne']
            ring
          rw [h1]
          have h2 := sub_div_le_log_div (n := m - 1) (m := m) (by omega) (by omega)
          have hcast : ((m : ℝ) - ((m - 1 : ℕ) : ℝ)) = 1 := by
            have h3 : (((m - 1 : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) := Nat.cast_inj.mpr (by omega)
            push_cast at h3; linarith
          rw [hcast] at h2
          exact h2
        have halg : 1 / (2 * a1 ^ 2) - 1 / (2 * a2 ^ 2) =
            (a2 - a1) * (a2 + a1) / (2 * a1 ^ 2 * a2 ^ 2) := by
          field_simp [ha1_pos.ne', ha2_pos.ne']; ring
        rw [halg]
        have hnum : (1 / (m : ℝ)) / a2 ^ 3 ≤ (a2 - a1) / a2 ^ 3 :=
          div_le_div_of_nonneg_right hdiff_ge (by positivity)
        have hstep : (a2 - a1) / a2 ^ 3 ≤ (a2 - a1) * (a2 + a1) / (2 * a1 ^ 2 * a2 ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h2a1 : 2 * a1 ^ 2 ≤ (a2 + a1) * a2 := by nlinarith
          have h2a : 2 * a1 ^ 2 * a2 ^ 2 ≤ (a2 + a1) * a2 ^ 3 := by
            have := mul_le_mul_of_nonneg_right h2a1 (sq_nonneg a2)
            linarith
          have hmul := mul_le_mul_of_nonneg_left h2a (sub_nonneg.mpr ha12)
          linarith
        calc 1 / ((m : ℝ) * a2 ^ 3)
            = (1 / (m : ℝ)) / a2 ^ 3 := by ring
          _ ≤ (a2 - a1) * (a2 + a1) / (2 * a1 ^ 2 * a2 ^ 2) := hnum.trans hstep
      have hS2_sub : S2 ⊆ Finset.Icc (2 * n + 1) N := by
        intro m hm
        simp only [S2, Finset.mem_filter, Finset.mem_Icc] at hm ⊢; omega
      have hsum_le : ∑ m ∈ S2, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤
          ∑ m ∈ Finset.Icc (2 * n + 1) N,
            (1 / (2 * (Real.log (((m - 1 : ℕ) : ℝ) / (n : ℝ))) ^ 2) -
             1 / (2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 2)) := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg hS2_sub fun m hm _ => ?_).trans
          (Finset.sum_le_sum fun m hm => htel m (by rw [Finset.mem_Icc] at hm; omega))
        have hm_gt : 2 * n < m := by rw [Finset.mem_Icc] at hm; omega
        have hlog_pos : 0 < Real.log ((m : ℝ) / (n : ℝ)) := Real.log_pos (by
          rw [one_lt_div hn0]
          have hcast : ((2 * n : ℕ) : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hm_gt
          push_cast at hcast; linarith)
        positivity
      have htel_sum : ∀ K : ℕ,
          ∑ m ∈ Finset.Icc (2 * n + 1) K,
            (1 / (2 * (Real.log (((m - 1 : ℕ) : ℝ) / (n : ℝ))) ^ 2) -
             1 / (2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 2)) ≤
          1 / (2 * (Real.log 2) ^ 2) := by
        intro K
        by_cases hK : K < 2 * n + 1
        · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
          positivity
        · push Not at hK
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          have hval : ∀ r : ℕ,
              ∑ m ∈ Finset.Icc (2 * n + 1) (2 * n + 1 + r),
                (1 / (2 * (Real.log (((m - 1 : ℕ) : ℝ) / (n : ℝ))) ^ 2) -
                 1 / (2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 2)) =
              1 / (2 * (Real.log (((2 * n : ℕ) : ℝ) / (n : ℝ))) ^ 2) -
              1 / (2 * (Real.log (((2 * n + 1 + r : ℕ) : ℝ) / (n : ℝ))) ^ 2) := by
            intro r
            induction r with
            | zero => simp
            | succ r ih =>
              have hIcc : Finset.Icc (2 * n + 1) (2 * n + 1 + (r + 1)) =
                  insert (2 * n + 1 + (r + 1)) (Finset.Icc (2 * n + 1) (2 * n + 1 + r)) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hIcc, Finset.sum_insert (by simp), ih]
              have hsub1 : (2 * n + 1 + (r + 1) - 1 : ℕ) = 2 * n + 1 + r := by omega
              rw [hsub1]; ring
          rw [hval d]
          have h2n : ((2 * n : ℕ) : ℝ) / (n : ℝ) = 2 := by push_cast; field_simp [hn0.ne']
          rw [h2n]
          have hnonneg : 0 ≤ 1 / (2 * (Real.log (((2 * n + 1 + d : ℕ) : ℝ) / (n : ℝ))) ^ 2) := by
            positivity
          linarith
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hinv_log2 : 1 / (2 * (Real.log 2) ^ 2) ≤ 2 := by
        have hsq : (1 / 4 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hn2_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
        nlinarith
      calc (1 / (n : ℝ) ^ 2) * ∑ m ∈ S2, 1 / ((m : ℝ) * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
          ≤ 1 * (1 / (2 * (Real.log 2) ^ 2)) := by
            refine mul_le_mul ?_ (hsum_le.trans (htel_sum N)) ?_ (by positivity)
            · exact (one_div_le_one_div_of_le zero_lt_one hn2_ge1).trans (by norm_num)
            · refine Finset.sum_nonneg fun m hm => ?_
              have hgt : 2 * n < m := (Finset.mem_filter.mp hm).2
              have hlp : 0 < Real.log ((m : ℝ) / (n : ℝ)) := Real.log_pos (by
                rw [one_lt_div hn0]
                have hcast : ((2 * n : ℕ) : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hgt
                push_cast at hcast; linarith)
              positivity
        _ ≤ 2 := by linarith
    linarith [hS1, hS2]
  have hcol_sum : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
        K m n * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)) ≤ 8 / 3 := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsimp : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
        K m n * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)) =
        (1 / 12) * (1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hn52 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
        norm_num
      dsimp only [K]
      rw [hn52]
      have hsq_n_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      have hsq_m_ne : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
      field_simp [hsq_n_ne, hsq_m_ne]
      rw [Real.sq_sqrt hn0.le]
    rw [Finset.sum_congr rfl hsimp, ← Finset.mul_sum]
    set T1 := ((Finset.Icc 1 N).filter (fun n => n < m)).filter (fun n => m ≤ 2 * n)
    set T2 := ((Finset.Icc 1 N).filter (fun n => n < m)).filter (fun n => 2 * n < m)
    have hpart : (Finset.Icc 1 N).filter (fun n => n < m) = T1 ∪ T2 := by
      ext n; simp only [T1, T2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; by_cases h2 : m ≤ 2 * n
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, by omega⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [T1, T2, Finset.mem_filter] at h1 h2; omega
    rw [hpart, Finset.sum_union hdisj]
    have hT1 : ∑ n ∈ T1, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤ 16 := by
      have hle : ∑ n ∈ T1, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤
          ∑ n ∈ T1, 8 / ((m : ℝ) - (n : ℝ)) ^ 3 := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [T1, Finset.mem_filter] at hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn.1.1).1
        have hnm : n < m := hn.1.2
        have hmn_pos : 0 < (m : ℝ) - (n : ℝ) := by
          have hlt : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
          linarith
        have hn_ge : (m : ℝ) / 2 ≤ (n : ℝ) := by
          have hcast : (m : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_le.mpr hn.2
          push_cast at hcast; linarith
        have hlog_ge := sub_div_le_log_div hn1 hnm
        have hden : ((m : ℝ) / 2) ^ 3 * (((m : ℝ) - (n : ℝ)) / (m : ℝ)) ^ 3 ≤
            (n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hn_ge 3)
            (pow_le_pow_left₀ (by positivity) hlog_ge 3) (by positivity) (by positivity)
        calc 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
            ≤ 1 / (((m : ℝ) / 2) ^ 3 * (((m : ℝ) - (n : ℝ)) / (m : ℝ)) ^ 3) :=
              one_div_le_one_div_of_le (by positivity) hden
          _ = 8 / ((m : ℝ) - (n : ℝ)) ^ 3 := by field_simp [hm0.ne', hmn_pos.ne']; ring
      calc ∑ n ∈ T1, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
          ≤ 8 * ∑ n ∈ T1, (1 : ℝ) / ((m : ℝ) - (n : ℝ)) ^ 3 := by
            rw [Finset.mul_sum]
            exact hle.trans_eq (Finset.sum_congr rfl fun n _ => by ring)
        _ ≤ 8 * ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ) ^ 3 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hinj : ∑ n ∈ T1, (1 : ℝ) / ((m : ℝ) - (n : ℝ)) ^ 3 =
                ∑ k ∈ T1.image (fun n => m - n), (1 : ℝ) / (k : ℝ) ^ 3 := by
              rw [Finset.sum_image]
              · refine Finset.sum_congr rfl fun n hn => ?_
                have hnm : n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
                rw [Nat.cast_sub hnm.le]
              · intro a ha b hb hab
                dsimp only at hab
                have ha' : a < m := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
                have hb' : b < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
                omega
            rw [hinj]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro k hk
            obtain ⟨n, hnT1, rfl⟩ := Finset.mem_image.mp hk
            simp only [T1, Finset.mem_filter, Finset.mem_Icc] at hnT1 ⊢; omega
        _ ≤ 8 * 2 := mul_le_mul_of_nonneg_left (sum_inv_cube_le_two m) (by positivity)
        _ = 16 := by norm_num
    have hT2 : ∑ n ∈ T2, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤ 16 := by
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hle : ∑ n ∈ T2, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) ≤
          8 * ∑ n ∈ T2, (1 : ℝ) / (n : ℝ) ^ 3 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [T2, Finset.mem_filter] at hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn.1.1).1
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        have h2nm : (2 : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
          rw [le_div_iff₀ hn0]
          have hcast : ((2 * n : ℕ) : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hn.2
          push_cast at hcast; linarith
        have hlog_ge : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) / (n : ℝ)) :=
          hlog2.trans (Real.log_le_log (by norm_num) h2nm)
        have hden : (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hlog_ge 3) (by positivity)
        calc 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
            ≤ 1 / ((n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 3) := one_div_le_one_div_of_le (by positivity) hden
          _ = 8 * (1 / (n : ℝ) ^ 3) := by ring
      have hsub : T2 ⊆ Finset.Icc 1 N := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      calc ∑ n ∈ T2, 1 / ((n : ℝ) ^ 3 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3)
          ≤ 8 * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 3 :=
            hle.trans (mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity))
        _ ≤ 8 * 2 := mul_le_mul_of_nonneg_left (sum_inv_cube_le_two N) (by positivity)
        _ = 16 := by norm_num
    linarith [hT1, hT2]
  have herr_bound :
      ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          a m * star (a n) * ((E m n : ℝ) : ℂ)‖ ≤
      5 * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by
    have hnorm_le :
        ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            a m * star (a n) * ((E m n : ℝ) : ℂ)‖ ≤
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            ‖a m‖ * ‖a n‖ * |E m n| := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
    have hsym_sum :
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, ‖a m‖ * ‖a n‖ * |E m n| =
        2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
            ‖a m‖ * ‖a n‖ * |E m n| := by
      have hsplit : ∀ m ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).erase m, ‖a m‖ * ‖a n‖ * |E m n| =
          (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m), ‖a m‖ * ‖a n‖ * |E m n|) +
          (∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n), ‖a m‖ * ‖a n‖ * |E m n|) := by
        intro m _
        have hpart : (Finset.Icc 1 N).erase m =
            (Finset.Icc 1 N).filter (fun n => n < m) ∪ (Finset.Icc 1 N).filter (fun n => m < n) := by
          ext n; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro ⟨hne, hn⟩
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inl ⟨hn, hlt⟩
            · exact Or.inr ⟨hn, hgt⟩
          · rintro (⟨hn, hlt⟩ | ⟨hn, hgt⟩)
            · exact ⟨hlt.ne, hn⟩
            · exact ⟨hgt.ne', hn⟩
        have hdisj : Disjoint ((Finset.Icc 1 N).filter (fun n => n < m))
            ((Finset.Icc 1 N).filter (fun n => m < n)) := by
          rw [Finset.disjoint_left]; intro n h1 h2
          simp only [Finset.mem_filter] at h1 h2; omega
        rw [hpart, Finset.sum_union hdisj]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hswap : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
            ‖a m‖ * ‖a n‖ * |E m n| =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m < n),
            ‖a n‖ * ‖a m‖ * |E n m| := by
        have hL : ∀ m ∈ Finset.Icc 1 N,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n), ‖a m‖ * ‖a n‖ * |E m n| =
            ∑ n ∈ Finset.Icc 1 N, if m < n then ‖a m‖ * ‖a n‖ * |E m n| else 0 := by
          intro m _; rw [Finset.sum_filter]
        rw [Finset.sum_congr rfl hL, Finset.sum_comm]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m hm => ?_
        by_cases hmn : m < n
        · rw [if_pos hmn, if_pos hmn]
          rw [hE_antisymm n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1, abs_neg]
          ring
        · rw [if_neg hmn, if_neg hmn]
      rw [hswap]; ring
    have hupper :
        2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
            ‖a m‖ * ‖a n‖ * |E m n| ≤
        (8 / 3) * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) * ‖a m‖ ^ 2) +
        (3 / 2) * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2) := by
      have h1 : 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
            ‖a m‖ * ‖a n‖ * |E m n| ≤
          ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
            ((m : ℝ) * ‖a m‖ ^ 2 * (K m n * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ))) +
             (n : ℝ) * ‖a n‖ ^ 2 * (K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n hn => ?_
        have hnI := (Finset.mem_filter.mp hn).1
        have hnm : n < m := (Finset.mem_filter.mp hn).2
        have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hm).1; omega)
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hnI).1; omega)
        have hE := hE_bound m hm n hnI hnm
        have hK_eq : (1 / 12) / ((n : ℝ) ^ 2 * (Real.log ((m : ℝ) / (n : ℝ))) ^ 3) =
            Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) * K m n := by
          dsimp only [K]
          have hn52 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]; norm_num
          rw [hn52]
          have hsq_m_ne : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
          have hsq_n_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
          field_simp [hsq_m_ne, hsq_n_ne]
        have hK_nonneg : 0 ≤ K m n := by
          dsimp only [K]
          have hlp : 0 < Real.log ((m : ℝ) / (n : ℝ)) := Real.log_pos (by
            rw [one_lt_div hn0]; exact Nat.cast_lt.mpr hnm)
          positivity
        have hstep1 : 2 * (‖a m‖ * ‖a n‖ * |E m n|) ≤
            2 * (Real.sqrt (m : ℝ) * ‖a m‖) * (Real.sqrt (n : ℝ) * ‖a n‖) * K m n := by
          have := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * (‖a m‖ * ‖a n‖))
          rw [hK_eq] at this; linarith
        have hr_pos : 0 < Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ) := by positivity
        set x : ℝ := Real.sqrt (m : ℝ) * ‖a m‖
        set y : ℝ := Real.sqrt (n : ℝ) * ‖a n‖
        set r : ℝ := Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)
        have hamgm : 2 * x * y ≤ x ^ 2 * r + y ^ 2 * r⁻¹ := by
          have hsq := sq_nonneg (x * Real.sqrt r - y / Real.sqrt r)
          have hsr_ne : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
          have hexp : (x * Real.sqrt r - y / Real.sqrt r) ^ 2 = x ^ 2 * r - 2 * x * y + y ^ 2 * r⁻¹ := by
            field_simp [hsr_ne]
            rw [Real.sq_sqrt hr_pos.le]
            field_simp [hr_pos.ne']; ring
          linarith
        have hx2 : x ^ 2 = (m : ℝ) * ‖a m‖ ^ 2 := by
          dsimp only [x]; rw [mul_pow, Real.sq_sqrt hm0.le]
        have hy2 : y ^ 2 = (n : ℝ) * ‖a n‖ ^ 2 := by
          dsimp only [y]; rw [mul_pow, Real.sq_sqrt hn0.le]
        have hrinv : r⁻¹ = Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ) := inv_div _ _
        calc 2 * (‖a m‖ * ‖a n‖ * |E m n|)
            ≤ (2 * x * y) * K m n := hstep1
          _ ≤ (x ^ 2 * r + y ^ 2 * r⁻¹) * K m n := mul_le_mul_of_nonneg_right hamgm hK_nonneg
          _ = (m : ℝ) * ‖a m‖ ^ 2 * (K m n * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ))) +
              (n : ℝ) * ‖a n‖ ^ 2 * (K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ))) := by
            rw [hx2, hy2, hrinv]; ring
      refine h1.trans ?_
      simp_rw [Finset.sum_add_distrib]
      refine add_le_add ?_ ?_
      · rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun m hm => ?_
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hcol_sum m hm) (by positivity : 0 ≤ (m : ℝ) * ‖a m‖ ^ 2)
        linarith
      · have hswap :
            ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
              (n : ℝ) * ‖a n‖ ^ 2 * (K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ))) =
            ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 *
              ∑ m ∈ (Finset.Icc 1 N).filter (fun m => n < m),
                K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)) := by
          have hL : ∀ m ∈ Finset.Icc 1 N,
              ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n < m),
                (n : ℝ) * ‖a n‖ ^ 2 * (K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ))) =
              ∑ n ∈ Finset.Icc 1 N,
                if n < m then (n : ℝ) * ‖a n‖ ^ 2 * (K m n * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)))
                else 0 := fun m _ => Finset.sum_filter _ _
          rw [Finset.sum_congr rfl hL, Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_filter, ← Finset.mul_sum]
        rw [hswap, Finset.mul_sum]
        refine Finset.sum_le_sum fun n hn => ?_
        have := mul_le_mul_of_nonneg_left (hrow_sum n hn) (by positivity : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2)
        linarith
    have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => by positivity
    linarith [hnorm_le, hsym_sum, hupper]
  rw [hdiff_eq]
  calc ‖(∑ p ∈ P, ∑ q ∈ P.erase p, b p * star (b q) / ((lam p - lam q : ℝ) : ℂ)) -
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            a m * star (a n) * ((E m n : ℝ) : ℂ))‖
      ≤ ‖∑ p ∈ P, ∑ q ∈ P.erase p, b p * star (b q) / ((lam p - lam q : ℝ) : ℂ)‖ +
        ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            a m * star (a n) * ((E m n : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 4 * Real.pi * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 +
        5 * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by
        rw [hRHS_eq] at hMV; exact add_le_add hMV herr_bound
    _ = (4 * Real.pi + 5) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by ring

/-! ## Section 2: Mean-Value Theorem & Discrete Large Sieve for Dirichlet Polynomials -/

/-- A Dirichlet polynomial `∑_{n=1}^N a n * n^(-s)`. -/
def dirichletPoly (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)

lemma nat_cpow_neg_I_mul (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  congr 1; ring

lemma norm_nat_cpow_neg_I_mul (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [nat_cpow_neg_I_mul n hn t,
    show -Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) =
      ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma integral_cexp_neg_I_mul (ω T : ℝ) (hω : ω ≠ 0) :
    ∫ t in (-T : ℝ)..T, Complex.exp (-Complex.I * (t : ℂ) * (ω : ℂ)) =
      (Complex.exp (Complex.I * (T : ℂ) * (ω : ℂ)) -
       Complex.exp (-Complex.I * (T : ℂ) * (ω : ℂ))) / (Complex.I * (ω : ℂ)) := by
  have hden : -Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hω)
  have hderiv : ∀ t ∈ Set.uIcc (-T) T,
      HasDerivAt (fun u : ℝ => Complex.exp (-Complex.I * (u : ℂ) * (ω : ℂ)) / (-Complex.I * (ω : ℂ)))
        (Complex.exp (-Complex.I * (t : ℂ) * (ω : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => -Complex.I * (u : ℂ) * (ω : ℂ)) (-Complex.I * (ω : ℂ)) t := by
      have hid := (hasDerivAt_id t).ofReal_comp
      have hmul := (hid.const_mul (-Complex.I)).mul_const (ω : ℂ)
      refine hmul.congr_deriv ?_
      simp only [Complex.ofReal_one, mul_one]
    have h2 := h1.cexp.div_const (-Complex.I * (ω : ℂ))
    refine h2.congr_deriv ?_
    exact mul_div_cancel_right₀ _ hden
  have hcont : Continuous (fun u : ℝ => Complex.exp (-Complex.I * (u : ℂ) * (ω : ℂ))) :=
    Complex.continuous_exp.comp (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable (-T) T)]
  have hneg : -Complex.I * ((-T : ℝ) : ℂ) * (ω : ℂ) = Complex.I * (T : ℂ) * (ω : ℂ) := by
    push_cast; ring
  rw [hneg]
  have hden' : Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  field_simp [hden, hden']
  ring

/-- **Unconditional Montgomery–Vaughan Mean-Value Theorem for Dirichlet Polynomials (Exact Bound)**:
for every `N : ℕ`, `T : ℝ`, and `a : ℕ → ℂ`,
`|(∫ t in (-T)..T, ‖dirichletPoly a N (I * t)‖ ^ 2) - 2 * T * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2| ≤ (8 * Real.pi + 10) * ∑ n ∈ Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2`. -/
theorem dirichletPoly_mean_value_exact_bound (N : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    |(∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2) -
        2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2| ≤
      (8 * Real.pi + 10) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by
  -- Expand `‖dirichletPoly a N (I * t)‖ ^ 2` into diagonal + off-diagonal exponential sum
  let off : ℝ → ℂ := fun t =>
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
      a m * star (a n) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / (n : ℝ)) : ℂ))
  have hpt : ∀ t : ℝ, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2 =
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) + (off t).re := by
    intro t
    have hnorm : (‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2 : ℝ) =
        (dirichletPoly a N (Complex.I * (t : ℂ)) * star (dirichletPoly a N (Complex.I * (t : ℂ)))).re := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hnorm]
    have hexp : dirichletPoly a N (Complex.I * (t : ℂ)) * star (dirichletPoly a N (Complex.I * (t : ℂ))) =
        ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 : ℝ) : ℂ) + off t := by
      dsimp only [dirichletPoly]
      rw [star_sum, Finset.sum_mul]
      have h1 : ∀ m ∈ Finset.Icc 1 N,
          a m * (m : ℂ) ^ (-(Complex.I * (t : ℂ))) *
            ∑ n ∈ Finset.Icc 1 N, star (a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
          ((‖a m‖ ^ 2 : ℝ) : ℂ) +
          ∑ n ∈ (Finset.Icc 1 N).erase m,
            a m * star (a n) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / (n : ℝ)) : ℂ)) := by
        intro m hm
        rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hm]
        congr 1
        · have hmn : ‖(m : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 :=
            norm_nat_cpow_neg_I_mul m (Finset.mem_Icc.mp hm).1 t
          have h2 : a m * (m : ℂ) ^ (-(Complex.I * (t : ℂ))) *
              star (a m * (m : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
              ((‖a m * (m : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          rw [h2, norm_mul, hmn, mul_one]
        · refine Finset.sum_congr rfl fun n hn => ?_
          have hnI := Finset.mem_of_mem_erase hn
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
          have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
          have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
          rw [star_mul', nat_cpow_neg_I_mul m hm1 t, nat_cpow_neg_I_mul n hn1 t]
          have hconj : star (Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) =
              Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
            rw [Complex.star_def, ← Complex.exp_conj]
            simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
          rw [hconj, Real.log_div hm0.ne' hn0.ne']
          calc a m * Complex.exp (-Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                (star (a n) * Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)))
              = a m * star (a n) *
                (Complex.exp (-Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                 Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by ring
            _ = a m * star (a n) *
                Complex.exp (-Complex.I * (t : ℂ) * ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)) := by
                rw [← Complex.exp_add]; congr 2; push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Complex.ofReal_sum]
    rw [hexp, Complex.add_re, Complex.ofReal_re]
  have hoff_cont : Continuous off := by
    refine continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun n _ => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
  have hint_eq : ∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2 =
      2 * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) + (∫ t in (-T : ℝ)..T, off t).re := by
    simp_rw [hpt]
    have hint_off_re : IntervalIntegrable (fun t => (off t).re) volume (-T) T :=
      (Complex.continuous_re.comp hoff_cont).intervalIntegrable (-T) T
    rw [intervalIntegral.integral_add intervalIntegrable_const hint_off_re,
      intervalIntegral.integral_const, smul_eq_mul]
    have hre_int : ∫ t in (-T : ℝ)..T, (off t).re = (∫ t in (-T : ℝ)..T, off t).re :=
      (Complex.reCLM.intervalIntegral_comp_comm (hoff_cont.intervalIntegrable (-T) T))
    rw [hre_int]; ring
  -- Evaluate `∫_{-T}^T off t dt` explicitly as a difference of two logarithmic Hilbert sums!
  let aPlus : ℕ → ℂ := fun n => a n * Complex.exp (Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ))
  let aMinus : ℕ → ℂ := fun n => a n * Complex.exp (-Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ))
  have hint_off : ∫ t in (-T : ℝ)..T, off t =
      (1 / Complex.I) *
        ((∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aPlus m * star (aPlus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)) -
         (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aMinus m * star (aMinus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ))) := by
    have hRHS_push :
        (1 / Complex.I) *
          ((∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              aPlus m * star (aPlus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)) -
           (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              aMinus m * star (aMinus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ))) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
          (1 / Complex.I) *
            (aPlus m * star (aPlus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ) -
             aMinus m * star (aMinus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hRHS_push]
    dsimp only [off]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hnI := Finset.mem_of_mem_erase hn
        have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
        have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hm).1; omega)
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hnI).1; omega)
        have hω_ne : Real.log ((m : ℝ) / (n : ℝ)) ≠ 0 := by
          intro h
          have h1 : (m : ℝ) / (n : ℝ) = 1 :=
            (Real.log_eq_zero.mp h).resolve_left (div_pos hm0 hn0).ne' |>.resolve_right
              (by linarith [div_pos hm0 hn0])
          have h2 : (m : ℝ) = (n : ℝ) := (div_eq_one_iff_eq hn0.ne').mp h1
          exact hnm (Nat.cast_injective h2).symm
        rw [intervalIntegral.integral_const_mul, integral_cexp_neg_I_mul _ T hω_ne]
        have hconjP : star (aPlus n) =
            star (a n) * Complex.exp (-Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
          dsimp only [aPlus]
          rw [star_mul', Complex.star_def, ← Complex.exp_conj]
          simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        have hconjM : star (aMinus n) =
            star (a n) * Complex.exp (Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
          dsimp only [aMinus]
          rw [star_mul', Complex.star_def, ← Complex.exp_conj]
          simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
        have hP : aPlus m * star (aPlus n) =
            a m * star (a n) * Complex.exp (Complex.I * (T : ℂ) * (Real.log ((m : ℝ) / (n : ℝ)) : ℂ)) := by
          rw [hconjP]; dsimp only [aPlus]
          rw [Real.log_div hm0.ne' hn0.ne']
          calc a m * Complex.exp (Complex.I * (T : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                (star (a n) * Complex.exp (-Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ)))
              = a m * star (a n) *
                (Complex.exp (Complex.I * (T : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                 Complex.exp (-Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ))) := by ring
            _ = a m * star (a n) *
                Complex.exp (Complex.I * (T : ℂ) * ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)) := by
                rw [← Complex.exp_add]; congr 2; push_cast; ring
        have hM : aMinus m * star (aMinus n) =
            a m * star (a n) * Complex.exp (-Complex.I * (T : ℂ) * (Real.log ((m : ℝ) / (n : ℝ)) : ℂ)) := by
          rw [hconjM]; dsimp only [aMinus]
          rw [Real.log_div hm0.ne' hn0.ne']
          calc a m * Complex.exp (-Complex.I * (T : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                (star (a n) * Complex.exp (Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ)))
              = a m * star (a n) *
                (Complex.exp (-Complex.I * (T : ℂ) * (Real.log (m : ℝ) : ℂ)) *
                 Complex.exp (Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ))) := by ring
            _ = a m * star (a n) *
                Complex.exp (-Complex.I * (T : ℂ) * ((Real.log (m : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ)) := by
                rw [← Complex.exp_add]; congr 2; push_cast; ring
        rw [hP, hM]
        have hωC : ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω_ne
        field_simp [Complex.I_ne_zero, hωC]
      · intro n _
        exact (continuous_const.mul (Complex.continuous_exp.comp
          ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).intervalIntegrable _ _
    · intro m _
      exact (continuous_finsetSum _ fun n _ => continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).intervalIntegrable _ _
  have hnorm_aP : ∀ n : ℕ, ‖aPlus n‖ = ‖a n‖ := by
    intro n; dsimp only [aPlus]
    rw [norm_mul,
      show Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ) =
        ((T * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnorm_aM : ∀ n : ℕ, ‖aMinus n‖ = ‖a n‖ := by
    intro n; dsimp only [aMinus]
    rw [norm_mul,
      show -Complex.I * (T : ℂ) * (Real.log (n : ℝ) : ℂ) =
        ((-(T * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hHP := hilbert_inequality_log N aPlus
  have hHM := hilbert_inequality_log N aMinus
  simp_rw [hnorm_aP] at hHP
  simp_rw [hnorm_aM] at hHM
  rw [hint_eq, add_sub_cancel_left]
  calc |(∫ t in (-T : ℝ)..T, off t).re|
      ≤ ‖∫ t in (-T : ℝ)..T, off t‖ := Complex.abs_re_le_norm _
    _ = ‖(∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aPlus m * star (aPlus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)) -
         (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aMinus m * star (aMinus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ))‖ := by
        rw [hint_off, norm_mul, norm_div, norm_one, Complex.norm_I, div_one, one_mul]
    _ ≤ ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aPlus m * star (aPlus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)‖ +
        ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            aMinus m * star (aMinus n) / ((Real.log ((m : ℝ) / (n : ℝ)) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (4 * Real.pi + 5) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 +
        (4 * Real.pi + 5) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := add_le_add hHP hHM
    _ = (8 * Real.pi + 10) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 := by ring

/-- Upper-bound corollary of the Montgomery–Vaughan Mean-Value Theorem:
`∫_{-T}^T ‖dirichletPoly a N (I * t)‖ ^ 2 dt ≤ (2 * T + (8 * Real.pi + 10) * N) * ∑_{n=1}^N ‖a n‖ ^ 2`. -/
theorem dirichletPoly_mean_value_upper (N : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    ∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2 ≤
      (2 * T + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h1 := (abs_le.mp (dirichletPoly_mean_value_exact_bound N T a)).2
  have h2 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (sq_nonneg _)
  have hC : 0 ≤ 8 * Real.pi + 10 := by positivity
  linarith [mul_le_mul_of_nonneg_left h2 hC]

/-- Asymptotic mean square of a fixed Dirichlet polynomial:
`(1 / (2 * T)) * ∫_{-T}^T ‖dirichletPoly a N (I * t)‖ ^ 2 dt → ∑_{n=1}^N ‖a n‖ ^ 2` as `T → ∞`. -/
theorem dirichletPoly_mean_value_tendsto (N : ℕ) (a : ℕ → ℂ) :
    Filter.Tendsto
      (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2)
      Filter.atTop (nhds (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) := by
  set M : ℝ := (8 * Real.pi + 10) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2
  set L : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (M / ε + 1), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTM : M / ε + 1 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  rw [Real.dist_eq]
  have hbd := dirichletPoly_mean_value_exact_bound N T a
  have hdiff : (1 / (2 * T)) * (∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2) - L =
      (1 / (2 * T)) * ((∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2) - 2 * T * L) := by
    field_simp [hTpos.ne']
  rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
  have hMnn : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => by positivity)
  calc (1 / (2 * T)) * |(∫ t in (-T : ℝ)..T, ‖dirichletPoly a N (Complex.I * (t : ℂ))‖ ^ 2) - 2 * T * L|
      ≤ (1 / (2 * T)) * M := mul_le_mul_of_nonneg_left hbd (by positivity)
    _ < ε := by
        rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity : 0 < 2 * T)]
        have hMlt : M < ε * T := by
          have := (div_lt_iff₀ hε).mp (by linarith : M / ε < T)
          linarith
        nlinarith

/-- **Sobolev–Gallagher Pointwise Lemma**:
for any `C^1` function `f : ℝ → ℂ` on `[t₀ - η, t₀ + η]` (`0 < η`),
`‖f t₀‖ ^ 2 ≤ (1 / (2 * η)) * ∫_{t₀ - η}^{t₀ + η} ‖f t‖ ^ 2 dt + 2 * ∫_{t₀ - η}^{t₀ + η} ‖f t‖ * ‖f' t‖ dt`. -/
theorem sobolev_gallagher_pointwise {f f' : ℝ → ℂ} {t₀ η : ℝ} (hη : 0 < η)
    (hderiv : ∀ t ∈ Set.Icc (t₀ - η) (t₀ + η), HasDerivAt f (f' t) t)
    (hcont' : ContinuousOn f' (Set.Icc (t₀ - η) (t₀ + η))) :
    ‖f t₀‖ ^ 2 ≤
      (1 / (2 * η)) * (∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2) +
      2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
  have hcont_f : ContinuousOn f (Set.Icc (t₀ - η) (t₀ + η)) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hcont_normsq : ContinuousOn (fun t => ‖f t‖ ^ 2) (Set.Icc (t₀ - η) (t₀ + η)) :=
    (continuous_norm.comp_continuousOn hcont_f).pow 2
  have hcont_prod : ContinuousOn (fun t => ‖f t‖ * ‖f' t‖) (Set.Icc (t₀ - η) (t₀ + η)) :=
    (continuous_norm.comp_continuousOn hcont_f).mul (continuous_norm.comp_continuousOn hcont')
  -- Derivative of `t ↦ ‖f t‖ ^ 2` is `2 * (f' t * star (f t)).re`
  have hderiv_sq : ∀ t ∈ Set.Icc (t₀ - η) (t₀ + η),
      HasDerivAt (fun u : ℝ => ‖f u‖ ^ 2) (2 * (f' t * star (f t)).re) t := by
    intro t ht
    have hf := hderiv t ht
    have hstar : HasDerivAt (fun u : ℝ => star (f u)) (star (f' t)) t := by
      have h1 : HasDerivAt (Complex.conjCLE ∘ f) (Complex.conjCLE (f' t)) t :=
        Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hf
      exact h1
    have hprod := hf.mul hstar
    have hre : HasDerivAt (fun u : ℝ => (f u * star (f u)).re)
        (f' t * star (f t) + f t * star (f' t)).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hprod
    have hfun : (fun u : ℝ => (f u * star (f u)).re) = fun u : ℝ => ‖f u‖ ^ 2 := by
      funext u
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hfun] at hre
    refine hre.congr_deriv ?_
    rw [Complex.add_re]
    have hconj_re : (f t * star (f' t)).re = (f' t * star (f t)).re := by
      have h1 : star (f' t * star (f t)) = f t * star (f' t) := by
        rw [star_mul', star_star, mul_comm]
      rw [← h1, Complex.star_def, Complex.conj_re]
    linarith
  have hcont_deriv_sq : ContinuousOn (fun t => 2 * (f' t * star (f t)).re) (Set.Icc (t₀ - η) (t₀ + η)) := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_)
    exact hcont'.mul (Complex.conjCLE.continuous.comp_continuousOn hcont_f)
  -- For every `u ∈ [t₀ - η, t₀ + η]`, `‖f t₀‖^2 - ‖f u‖^2 ≤ 2 * ∫_{t₀-η}^{t₀+η} ‖f‖ * ‖f'‖`
  have hpt_u : ∀ u ∈ Set.Icc (t₀ - η) (t₀ + η),
      ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 ≤ 2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
    intro u hu
    have huIcc : Set.uIcc u t₀ ⊆ Set.Icc (t₀ - η) (t₀ + η) :=
      Set.uIcc_subset_Icc hu ⟨by linarith, by linarith⟩
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv_sq t (huIcc ht))
      ((hcont_deriv_sq.mono huIcc).intervalIntegrable)
    rw [← hftc]
    have hle_abs : ∫ t in u..t₀, 2 * (f' t * star (f t)).re ≤
        ∫ t in (min u t₀)..(max u t₀), |2 * (f' t * star (f t)).re| := by
      rcases le_total u t₀ with hle | hge
      · rw [min_eq_left hle, max_eq_right hle]
        exact intervalIntegral.integral_mono_on hle
          ((hcont_deriv_sq.mono huIcc).intervalIntegrable)
          ((continuous_abs.comp_continuousOn (hcont_deriv_sq.mono huIcc)).intervalIntegrable)
          (fun t _ => le_abs_self _)
      · rw [min_eq_right hge, max_eq_left hge, intervalIntegral.integral_symm t₀ u]
        calc -(∫ t in t₀..u, 2 * (f' t * star (f t)).re)
            ≤ |∫ t in t₀..u, 2 * (f' t * star (f t)).re| := neg_le_abs _
          _ ≤ ∫ t in t₀..u, |2 * (f' t * star (f t)).re| :=
              intervalIntegral.abs_integral_le_integral_abs hge
    have hle_prod : ∫ t in (min u t₀)..(max u t₀), |2 * (f' t * star (f t)).re| ≤
        ∫ t in (min u t₀)..(max u t₀), 2 * (‖f t‖ * ‖f' t‖) := by
      have hsub : Set.uIcc (min u t₀) (max u t₀) ⊆ Set.Icc (t₀ - η) (t₀ + η) := by
        rw [Set.uIcc_of_le (min_le_max)]; exact Set.Icc_subset_Icc (le_min hu.1 (by linarith)) (max_le hu.2 (by linarith))
      refine intervalIntegral.integral_mono_on min_le_max
        ((continuous_abs.comp_continuousOn (hcont_deriv_sq.mono hsub)).intervalIntegrable)
        ((continuousOn_const.mul (hcont_prod.mono hsub)).intervalIntegrable) fun t _ => ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hre : |(f' t * star (f t)).re| ≤ ‖f t‖ * ‖f' t‖ := by
        calc |(f' t * star (f t)).re| ≤ ‖f' t * star (f t)‖ := Complex.abs_re_le_norm _
          _ = ‖f' t‖ * ‖f t‖ := by rw [norm_mul, norm_star]
          _ = ‖f t‖ * ‖f' t‖ := mul_comm _ _
      linarith
    have hle_full : ∫ t in (min u t₀)..(max u t₀), 2 * (‖f t‖ * ‖f' t‖) ≤
        2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
      have hlo : t₀ - η ≤ min u t₀ := le_min hu.1 (by linarith)
      have hhi : max u t₀ ≤ t₀ + η := max_le hu.2 (by linarith)
      have hint_full : IntervalIntegrable (fun t => 2 * (‖f t‖ * ‖f' t‖)) volume (t₀ - η) (t₀ + η) :=
        (continuousOn_const.mul hcont_prod).intervalIntegrable_of_Icc (by linarith)
      rw [← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le min_le_max, intervalIntegral.integral_of_le (by linarith)]
      refine setIntegral_mono_set ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hint_full)
        (ae_of_all _ fun t => by positivity) (Eventually.of_forall (Set.Ioc_subset_Ioc hlo hhi))
    linarith
  -- Average `hpt_u` over `u ∈ [t₀ - η, t₀ + η]`
  have havg : ∫ u in (t₀ - η)..(t₀ + η), (‖f t₀‖ ^ 2 - ‖f u‖ ^ 2) ≤
      ∫ u in (t₀ - η)..(t₀ + η), (2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖) :=
    intervalIntegral.integral_mono_on (by linarith : t₀ - η ≤ t₀ + η)
      (intervalIntegrable_const.sub (hcont_normsq.intervalIntegrable_of_Icc (by linarith)))
      intervalIntegrable_const hpt_u
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hcont_normsq.intervalIntegrable_of_Icc (by linarith)),
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at havg
  have hlen : t₀ + η - (t₀ - η) = 2 * η := by ring
  rw [hlen] at havg
  have hdiv := div_le_div_of_nonneg_right havg (by positivity : (0 : ℝ) ≤ 2 * η)
  have h2η : (2 * η) ≠ 0 := by positivity
  have hLHS : (2 * η * ‖f t₀‖ ^ 2 - ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2) / (2 * η) =
      ‖f t₀‖ ^ 2 - (1 / (2 * η)) * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ ^ 2 := by
    field_simp [h2η]
  have hRHS : (2 * η * (2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖)) / (2 * η) =
      2 * ∫ t in (t₀ - η)..(t₀ + η), ‖f t‖ * ‖f' t‖ := by
    field_simp [h2η]
  rw [hLHS, hRHS] at hdiv
  linarith

/-- **Unconditional Discrete Large-Sieve Mean-Value Theorem for Dirichlet Polynomials**:
for every `N ≥ 1`, `T ≥ 0`, `δ > 0`, `a : ℕ → ℂ`, and any `δ`-well-spaced finite collection
of points `t r ∈ [-T, T]` (`r ∈ S`),
`∑ r ∈ S, ‖dirichletPoly a N (I * t r)‖ ^ 2 ≤ (16 * Real.pi + 24) * (T + N) * (δ⁻¹ + Real.log (2 * N)) * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2`. -/
theorem dirichletPoly_discrete_large_sieve {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t : ι → ℝ) {N : ℕ} (hN : 1 ≤ N) {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hbd : ∀ r ∈ S, |t r| ≤ T)
    (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |t r - t s|)
    (a : ℕ → ℂ) :
    ∑ r ∈ S, ‖dirichletPoly a N (Complex.I * (t r : ℂ))‖ ^ 2 ≤
      (16 * Real.pi + 24) * (T + (N : ℝ)) * (δ⁻¹ + Real.log (2 * (N : ℝ))) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog2N_ge : (1 / 2 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    have h2N : (2 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN; linarith
    exact hlog2.trans (Real.log_le_log (by norm_num) h2N)
  have hlog2N_pos : 0 < Real.log (2 * (N : ℝ)) := by linarith
  have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Case 1: `S.card ≤ 1` (handles `δ > 2 * T` cleanly!)
  by_cases hcard : S.card ≤ 1
  · by_cases hne : S = ∅
    · subst hne; simp only [Finset.sum_empty]; positivity
    · obtain ⟨r₀, hr₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hS_eq : S = {r₀} := by
        ext x
        simp only [Finset.mem_singleton]
        constructor
        · intro hx; exact Finset.card_le_one.mp hcard x hx r₀ hr₀
        · rintro rfl; exact hr₀
      rw [hS_eq, Finset.sum_singleton]
      -- Cauchy–Schwarz: `‖∑_{n=1}^N a n * n^(-I*t)‖^2 ≤ N * ∑_{n=1}^N ‖a n‖^2`
      have hcs : ‖dirichletPoly a N (Complex.I * (t r₀ : ℂ))‖ ^ 2 ≤
          (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
        have h1 : ‖dirichletPoly a N (Complex.I * (t r₀ : ℂ))‖ ≤
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
          dsimp only [dirichletPoly]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
          rw [norm_mul, norm_nat_cpow_neg_I_mul n (Finset.mem_Icc.mp hn).1 (t r₀), mul_one]
        have h2 : (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2 ≤
            ((Finset.Icc 1 N).card : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
          have hcs' := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) (fun _ => (1 : ℝ)) (fun n => ‖a n‖)
          simpa using hcs'
        have hcardIcc : (Finset.Icc 1 N).card = N := by simp
        rw [hcardIcc] at h2
        exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
      have hcoeff : (N : ℝ) ≤ (16 * Real.pi + 24) * (T + (N : ℝ)) * (δ⁻¹ + Real.log (2 * (N : ℝ))) := by
        have h1 : 1 ≤ (16 * Real.pi + 24) * (δ⁻¹ + Real.log (2 * (N : ℝ))) := by
          have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
          have hdinv : 0 < δ⁻¹ := inv_pos.mpr hδ
          nlinarith
        nlinarith
      exact hcs.trans (mul_le_mul_of_nonneg_right hcoeff hsum_nn)
  -- Case 2: `2 ≤ S.card`, so `δ ≤ 2 * T`!
  · push Not at hcard
    have hδ_le_2T : δ ≤ 2 * T := by
      obtain ⟨r₁, hr₁, r₂, hr₂, hrne⟩ := Finset.one_lt_card.mp hcard
      have h1 := hsep r₁ hr₁ r₂ hr₂ hrne
      have h2 := hbd r₁ hr₁
      have h3 := hbd r₂ hr₂
      calc δ ≤ |t r₁ - t r₂| := h1
        _ ≤ |t r₁| + |t r₂| := abs_sub _ _
        _ ≤ T + T := add_le_add h2 h3
        _ = 2 * T := by ring
    set η : ℝ := δ / 2
    have hη_eq : η = δ / 2 := rfl
    have hη : 0 < η := by positivity
    set T' : ℝ := T + η
    have hT'_le : T' ≤ 2 * T := by dsimp only [T', η]; linarith
    -- Define `f u := dirichletPoly a N (I * u)` and its exact derivative `f' u`
    let a' : ℕ → ℂ := fun n => (-Complex.I * (Real.log (n : ℝ) : ℂ)) * a n
    let f : ℝ → ℂ := fun u => dirichletPoly a N (Complex.I * (u : ℂ))
    let f' : ℝ → ℂ := fun u => dirichletPoly a' N (Complex.I * (u : ℂ))
    have hf_deriv : ∀ u : ℝ, HasDerivAt f (f' u) u := by
      intro u
      dsimp only [f, f', dirichletPoly, a']
      have hterm : ∀ n ∈ Finset.Icc 1 N,
          HasDerivAt (fun x : ℝ => a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ))))
            ((-Complex.I * (Real.log (n : ℝ) : ℂ)) * a n * (n : ℂ) ^ (-(Complex.I * (u : ℂ)))) u := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hfun : (fun x : ℝ => a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))) =
            fun x : ℝ => a n * Complex.exp (-Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
          funext x; rw [nat_cpow_neg_I_mul n hn1 x]
        rw [hfun]
        have hlin : HasDerivAt (fun x : ℝ => -Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ))
            (-Complex.I * (Real.log (n : ℝ) : ℂ)) u := by
          have hid := (hasDerivAt_id u).ofReal_comp
          refine ((hid.const_mul (-Complex.I)).mul_const (Real.log (n : ℝ) : ℂ)).congr_deriv ?_
          simp only [Complex.ofReal_one, mul_one]
        have hce := (hlin.cexp).const_mul (a n)
        refine hce.congr_deriv ?_
        rw [nat_cpow_neg_I_mul n hn1 u]; ring
      exact HasDerivAt.fun_sum hterm
    have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf_deriv u).continuousAt
    have hf'_cont : Continuous f' := by
      dsimp only [f', dirichletPoly]
      refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
      have hfun : (fun x : ℝ => (n : ℂ) ^ (-(Complex.I * (x : ℂ)))) =
          fun x : ℝ => Complex.exp (-Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        funext x; exact nat_cpow_neg_I_mul n (Finset.mem_Icc.mp hn).1 x
      rw [hfun]
      exact Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    -- Apply `sobolev_gallagher_pointwise` to each `r ∈ S` and use disjointness of `(t r - η, t r + η) ⊆ [-T', T']`!
    have hdisj_sum : ∀ g : ℝ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
        ∑ r ∈ S, (∫ u in (t r - η)..(t r + η), g u) ≤ ∫ u in (-T')..T', g u := by
      intro g hg hgnn
      have h1 : ∀ r ∈ S, ∫ u in (t r - η)..(t r + η), g u =
          ∫ u in Set.Ioo (t r - η) (t r + η), g u := by
        intro r _
        rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [Finset.sum_congr rfl h1]
      have hdisj : Set.PairwiseDisjoint (S : Set ι) (fun r => Set.Ioo (t r - η) (t r + η)) := by
        intro r hr s hs hrs
        rw [Function.onFun, Set.disjoint_left]
        intro x hxr hxs
        have hsep' := hsep r hr s hs hrs
        rcases le_or_gt (t r) (t s) with hle | hgt
        · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hsep'
          linarith [hxr.2, hxs.1, hη_eq]
        · rw [abs_of_pos (sub_pos.mpr hgt)] at hsep'
          linarith [hxs.2, hxr.1, hη_eq]
      have hmeas : ∀ r ∈ S, MeasurableSet (Set.Ioo (t r - η) (t r + η)) :=
        fun _ _ => measurableSet_Ioo
      have hint_T' : IntegrableOn g (Set.Ioc (-T') T') :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hT, hη])).mp
          (hg.intervalIntegrable (-T') T')
      have hsub : ∀ r ∈ S, Set.Ioo (t r - η) (t r + η) ⊆ Set.Ioc (-T') T' := by
        intro r hr x hx
        have htr := abs_le.mp (hbd r hr)
        exact ⟨by linarith [hx.1, htr.1], by linarith [hx.2, htr.2]⟩
      have hint_r : ∀ r ∈ S, IntegrableOn g (Set.Ioo (t r - η) (t r + η)) :=
        fun r hr => hint_T'.mono_set (hsub r hr)
      rw [← MeasureTheory.integral_biUnion_finset S hmeas hdisj hint_r]
      rw [intervalIntegral.integral_of_le (by linarith [hT, hη])]
      refine setIntegral_mono_set hint_T' (ae_of_all _ hgnn) (Eventually.of_forall ?_)
      exact Set.iUnion₂_subset hsub
    have hsg : ∑ r ∈ S, ‖f (t r)‖ ^ 2 ≤
        δ⁻¹ * (∫ u in (-T')..T', ‖f u‖ ^ 2) + 2 * ∫ u in (-T')..T', ‖f u‖ * ‖f' u‖ := by
      have hpt : ∀ r ∈ S, ‖f (t r)‖ ^ 2 ≤
          δ⁻¹ * (∫ u in (t r - η)..(t r + η), ‖f u‖ ^ 2) +
          2 * ∫ u in (t r - η)..(t r + η), ‖f u‖ * ‖f' u‖ := by
        intro r _
        have h := sobolev_gallagher_pointwise (f := f) (f' := f') (t₀ := t r) hη
          (fun u _ => hf_deriv u) hf'_cont.continuousOn
        have h2η : 1 / (2 * η) = δ⁻¹ := by dsimp only [η]; field_simp [hδ.ne']
        rwa [h2η] at h
      calc ∑ r ∈ S, ‖f (t r)‖ ^ 2
          ≤ ∑ r ∈ S, (δ⁻¹ * (∫ u in (t r - η)..(t r + η), ‖f u‖ ^ 2) +
              2 * ∫ u in (t r - η)..(t r + η), ‖f u‖ * ‖f' u‖) := Finset.sum_le_sum hpt
        _ = δ⁻¹ * (∑ r ∈ S, ∫ u in (t r - η)..(t r + η), ‖f u‖ ^ 2) +
            2 * (∑ r ∈ S, ∫ u in (t r - η)..(t r + η), ‖f u‖ * ‖f' u‖) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ δ⁻¹ * (∫ u in (-T')..T', ‖f u‖ ^ 2) + 2 * ∫ u in (-T')..T', ‖f u‖ * ‖f' u‖ := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left
                (hdisj_sum _ (hf_cont.norm.pow 2) (fun _ => sq_nonneg _)) (by positivity)
            · exact mul_le_mul_of_nonneg_left
                (hdisj_sum _ (hf_cont.norm.mul hf'_cont.norm) (fun _ => by positivity)) (by norm_num)
    -- Apply `2 * ‖f u‖ * ‖f' u‖ ≤ α * ‖f u‖ ^ 2 + α⁻¹ * ‖f' u‖ ^ 2` with `α = Real.log (2 * N)`
    set α : ℝ := Real.log (2 * (N : ℝ))
    have hcs_int : 2 * ∫ u in (-T')..T', ‖f u‖ * ‖f' u‖ ≤
        α * (∫ u in (-T')..T', ‖f u‖ ^ 2) + α⁻¹ * (∫ u in (-T')..T', ‖f' u‖ ^ 2) := by
      have h1 : ∀ u ∈ Set.Icc (-T') T', 2 * (‖f u‖ * ‖f' u‖) ≤ α * ‖f u‖ ^ 2 + α⁻¹ * ‖f' u‖ ^ 2 := by
        intro u _
        have hsq := sq_nonneg (Real.sqrt α * ‖f u‖ - ‖f' u‖ / Real.sqrt α)
        have hsqα : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hlog2N_pos).ne'
        have hexp : (Real.sqrt α * ‖f u‖ - ‖f' u‖ / Real.sqrt α) ^ 2 =
            α * ‖f u‖ ^ 2 - 2 * (‖f u‖ * ‖f' u‖) + α⁻¹ * ‖f' u‖ ^ 2 := by
          field_simp [hsqα]
          rw [Real.sq_sqrt hlog2N_pos.le]
          field_simp [hlog2N_pos.ne']; ring
        linarith
      have hint1 : IntervalIntegrable (fun u : ℝ => 2 * (‖f u‖ * ‖f' u‖)) volume (-T') T' :=
        (continuous_const.mul (hf_cont.norm.mul hf'_cont.norm)).intervalIntegrable (-T') T'
      have hint2a : IntervalIntegrable (fun u : ℝ => α * ‖f u‖ ^ 2) volume (-T') T' :=
        (continuous_const.mul (hf_cont.norm.pow 2)).intervalIntegrable (-T') T'
      have hint2b : IntervalIntegrable (fun u : ℝ => α⁻¹ * ‖f' u‖ ^ 2) volume (-T') T' :=
        (continuous_const.mul (hf'_cont.norm.pow 2)).intervalIntegrable (-T') T'
      have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith [hT, hη] : -T' ≤ T')
        hint1 (hint2a.add hint2b) h1
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint2a hint2b,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
      exact hmono
    -- Apply `dirichletPoly_mean_value_upper` to `f` and `f'` on `[-T', T']`!
    have hmv_f := dirichletPoly_mean_value_upper N T' a
    have hmv_f' := dirichletPoly_mean_value_upper N T' a'
    have hnorm_a' : ∑ n ∈ Finset.Icc 1 N, ‖a' n‖ ^ 2 ≤ α ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      dsimp only [a']
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow]
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn1)
      have hlog_le : Real.log (n : ℝ) ≤ α := Real.log_le_log (Nat.cast_pos.mpr (by omega))
        (by have : (n : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hnN; linarith)
      rw [abs_of_nonneg hlog_nn]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog_nn hlog_le 2) (sq_nonneg _)
    have hmv_f'_le : ∫ u in (-T')..T', ‖f' u‖ ^ 2 ≤
        (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * α ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      have hC : 0 ≤ 2 * T' + (8 * Real.pi + 10) * (N : ℝ) := by positivity
      calc ∫ u in (-T')..T', ‖f' u‖ ^ 2
          ≤ (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a' n‖ ^ 2 := hmv_f'
        _ ≤ (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * (α ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hnorm_a' hC
        _ = (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * α ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring
    have hT'_bd : 2 * T' + (8 * Real.pi + 10) * (N : ℝ) ≤ (8 * Real.pi + 12) * (T + (N : ℝ)) := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      nlinarith
    have hcomb : ∑ r ∈ S, ‖f (t r)‖ ^ 2 ≤
        (δ⁻¹ + 2 * α) * ((2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
      have h1 : α⁻¹ * ((2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * α ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) =
          α * ((2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
        field_simp [hlog2N_pos.ne']
      have h2 := mul_le_mul_of_nonneg_left hmv_f (by positivity : 0 ≤ δ⁻¹ + α)
      have h3 := mul_le_mul_of_nonneg_left hmv_f'_le (by positivity : 0 ≤ α⁻¹)
      rw [h1] at h3
      linarith [hsg, hcs_int]
    have hfinal : (δ⁻¹ + 2 * α) * (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) ≤
        (16 * Real.pi + 24) * (T + (N : ℝ)) * (δ⁻¹ + α) := by
      have h1 : δ⁻¹ + 2 * α ≤ 2 * (δ⁻¹ + α) := by linarith [inv_pos.mpr hδ]
      have h2 : (δ⁻¹ + 2 * α) * (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) ≤
          (2 * (δ⁻¹ + α)) * ((8 * Real.pi + 12) * (T + (N : ℝ))) :=
        mul_le_mul h1 hT'_bd (by positivity) (by positivity)
      linarith
    calc ∑ r ∈ S, ‖f (t r)‖ ^ 2
        ≤ (δ⁻¹ + 2 * α) * (2 * T' + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
          linarith
      _ ≤ (16 * Real.pi + 24) * (T + (N : ℝ)) * (δ⁻¹ + α) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hfinal hsum_nn

/-! ## Section 3: Unconditional Second Moment of `riemannZeta` on `Re(s) > 1/2` -/

/-- Periodized second Bernoulli function `P_2(u) = (1 / 2) * ({u}^2 - {u} + 1 / 6)`. -/
def periodB2 (u : ℝ) : ℝ :=
  (1 / 2) * ((Stage5ZetaZeroFree.fractNat u) ^ 2 - Stage5ZetaZeroFree.fractNat u + 1 / 6)

lemma periodB2_nat (m : ℕ) : periodB2 (m : ℝ) = 1 / 12 := by
  dsimp only [periodB2, Stage5ZetaZeroFree.fractNat]
  rw [Nat.floor_natCast]
  ring

lemma abs_periodB2_le (u : ℝ) (hu : 0 ≤ u) : |periodB2 u| ≤ 1 / 12 := by
  dsimp only [periodB2]
  set x := Stage5ZetaZeroFree.fractNat u
  have hx0 : 0 ≤ x := Stage5ZetaZeroFree.fractNat_nonneg hu
  have hx1 : x ≤ 1 := (Stage5ZetaZeroFree.fractNat_lt_one u).le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - 1 / 2)]

lemma measurable_periodB2 : Measurable periodB2 := by
  unfold periodB2
  have hf := Stage5ZetaZeroFree.measurable_fractNat
  exact measurable_const.mul (((hf.pow_const 2).sub hf).add measurable_const)

/-- Helper: `u ↦ (u : ℂ) ^ w` is continuous on `Ioi a` for `a > 0`. -/
lemma continuousOn_ofReal_cpow_Ioi {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ w) (Ioi a) := by
  have hce : ContinuousOn (fun u : ℝ => Complex.exp ((Real.log u : ℂ) * w)) (Ioi a) :=
    ContinuousOn.cexp ((Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun u hu => (ha.trans hu).ne')).mul continuousOn_const)
  refine hce.congr fun u hu => ?_
  have hu0 : 0 < u := ha.trans hu
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'), ← Complex.ofReal_log hu0.le]

/-- Absolutely convergent Fourier cosine series of `periodB2 u` for all `u ≥ 0`:
`periodB2 u = ∑' k : ℕ, (1 / (2 * π^2 * k^2)) * cos(2 * π * k * u)`. -/
lemma hasSum_periodB2_fourier {u : ℝ} (hu : 0 ≤ u) :
    HasSum (fun k : ℕ => (1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * Real.cos (2 * Real.pi * (k : ℝ) * u))
      (periodB2 u) := by
  set x := Stage5ZetaZeroFree.fractNat u
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Stage5ZetaZeroFree.fractNat_nonneg hu, (Stage5ZetaZeroFree.fractNat_lt_one u).le⟩
  have hbase := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hbern : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval x =
      x ^ 2 - x + 1 / 6 := by
    have h1 := bernoulliFun_two x
    rw [bernoulliFun] at h1
    simpa [one_div] using h1
  rw [hbern] at hbase
  have hval : (-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ) *
      (x ^ 2 - x + 1 / 6) = Real.pi ^ 2 * (x ^ 2 - x + 1 / 6) := by
    have hfac : ((2 * 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac]; ring
  rw [hval] at hbase
  have hdiv := hbase.div_const (2 * Real.pi ^ 2)
  have htarget : Real.pi ^ 2 * (x ^ 2 - x + 1 / 6) / (2 * Real.pi ^ 2) = periodB2 u := by
    dsimp only [periodB2, x]
    field_simp [Real.pi_ne_zero]
  rw [htarget] at hdiv
  refine hdiv.congr_fun fun k => ?_
  have hcos : Real.cos (2 * Real.pi * (k : ℝ) * x) = Real.cos (2 * Real.pi * (k : ℝ) * u) := by
    dsimp only [x, Stage5ZetaZeroFree.fractNat]
    have hshift : 2 * Real.pi * (k : ℝ) * (u - (⌊u⌋₊ : ℝ)) =
        2 * Real.pi * (k : ℝ) * u - ((k * ⌊u⌋₊ : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [hshift]
    simpa [sub_eq_add_neg, neg_mul] using
      Real.cos_sub_int_mul_two_pi (2 * Real.pi * (k : ℝ) * u) (k * ⌊u⌋₊ : ℤ)
  rw [hcos]
  have hpow : (2 * 1 : ℕ) = 2 := rfl
  rw [hpow]
  ring

/-- Integration by parts of the Euler–Maclaurin remainder `∫_N^∞ ({t} - 1/2) t^(-s-1) dt`:
equals `-(1/12) * N^(-s-1) + (s + 1) * ∫_N^∞ periodB2(t) * t^(-s-2) dt` for `1 ≤ N`, `0 < s.re`. -/
lemma integral_fractNat_sub_half_ibp {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (N : ℝ), (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) =
      -(1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1) +
        (s + 1) * ∫ t in Ioi (N : ℝ), ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
  have hint_lhs : IntegrableOn
      (fun t : ℝ => (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)))
      (Ioi (N : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => (t : ℝ) ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hN0
    refine hdom.mono' ?_ ?_
    · have hm1 : AEStronglyMeasurable
          (fun t : ℝ => ((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ)) (volume.restrict (Ioi (N : ℝ))) :=
        (Complex.measurable_ofReal.comp (Stage5ZetaZeroFree.measurable_fractNat.sub measurable_const)).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (N : ℝ))) :=
        (continuousOn_ofReal_cpow_Ioi hN0 (-s - 1)).aestronglyMeasurable measurableSet_Ioi
      exact hm1.mul hm2
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht0 : 0 < t := hN0.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      have hfr_le : |Stage5ZetaZeroFree.fractNat t - 1 / 2| ≤ 1 := by
        have h0 := Stage5ZetaZeroFree.fractNat_nonneg ht0.le
        have h1 := Stage5ZetaZeroFree.fractNat_lt_one t
        rw [abs_le]; constructor <;> linarith
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hfr_le
  have hint_rhs : IntegrableOn
      (fun t : ℝ => ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2)) (Ioi (N : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => (t : ℝ) ^ (-s.re - 2)) (Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hN0
    refine hdom.mono' ?_ ?_
    · exact (Complex.measurable_ofReal.comp measurable_periodB2).aestronglyMeasurable.mul
        ((continuousOn_ofReal_cpow_Ioi hN0 (-s - 2)).aestronglyMeasurable measurableSet_Ioi)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht0 : 0 < t := hN0.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-s - 2).re = -s.re - 2 := by simp
      rw [hre]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _)
        ((abs_periodB2_le t ht0.le).trans (by norm_num))
  -- Single unit-interval IBP identity on `[m, m + 1]` for every `m ≥ N`
  have hunit : ∀ m : ℕ, N ≤ m →
      ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ),
        (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) =
      (1 / 12 : ℂ) * (((m + 1 : ℕ) : ℂ) ^ (-s - 1) - (m : ℂ) ^ (-s - 1)) +
        (s + 1) * ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ),
          ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr (le_trans hN hm)
    have hm0 : (0 : ℝ) < (m : ℝ) := zero_lt_one.trans_le hm1
    have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ m)
    -- Smooth polynomial version on `[m, m + 1]`
    let q : ℝ → ℝ := fun u => (1 / 2) * ((u - (m : ℝ)) ^ 2 - (u - (m : ℝ)) + 1 / 6)
    let q' : ℝ → ℝ := fun u => u - (m : ℝ) - 1 / 2
    let H : ℝ → ℂ := fun u => ((q u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
    let H' : ℝ → ℂ := fun u =>
      ((q' u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) - (s + 1) * (((q u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
    have hderiv : ∀ u ∈ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ), HasDerivAt H (H' u) u := by
      intro u hu
      rw [Set.uIcc_of_le hle] at hu
      have hu0 : 0 < u := lt_of_lt_of_le hm0 hu.1
      have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
      have hq : HasDerivAt (fun x : ℝ => ((q x : ℝ) : ℂ)) ((q' u : ℝ) : ℂ) u := by
        have hqR : HasDerivAt q (q' u) u := by
          dsimp only [q, q']
          have h1 : HasDerivAt (fun x : ℝ => x - (m : ℝ)) 1 u :=
            (hasDerivAt_id u).sub_const (m : ℝ)
          have h2 := ((h1.pow 2).sub h1).add_const (1 / 6 : ℝ)
          have h3 := h2.const_mul (1 / 2 : ℝ)
          refine h3.congr_deriv ?_; ring
        exact hqR.ofReal_comp
      have hpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 1)) ((-s - 1) * (u : ℂ) ^ (-s - 2)) u := by
        have hfun : (fun x : ℝ => (x : ℂ) ^ (-s - 1)) =ᶠ[𝓝 u]
            fun x : ℝ => Complex.exp ((Real.log x : ℂ) * (-s - 1)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hu0] with x hx
          have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
          rw [Complex.cpow_def_of_ne_zero hxC, Complex.ofReal_log hx.le]
        have h1 : HasDerivAt (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * (-s - 1)))
            (Complex.exp ((Real.log u : ℂ) * (-s - 1)) * (((u⁻¹ : ℝ) : ℂ) * (-s - 1))) u :=
          (((Real.hasDerivAt_log hu0.ne').ofReal_comp).mul_const (-s - 1)).cexp
        refine (h1.congr_of_eventuallyEq hfun).congr_deriv ?_
        have hcp : Complex.exp ((Real.log u : ℂ) * (-s - 1)) = (u : ℂ) ^ (-s - 1) := by
          rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu0.le]
        have hsub1 : (u : ℂ) ^ (-s - 2) = (u : ℂ) ^ (-s - 1) / (u : ℂ) := by
          rw [show (-s - 2 : ℂ) = (-s - 1) - 1 by ring, Complex.cpow_sub _ _ huC, Complex.cpow_one]
        rw [hcp, hsub1]
        push_cast; field_simp [huC]
      refine (hq.mul hpow).congr_deriv ?_
      dsimp only [H']; ring
    have hcont_pow : ∀ w : ℂ, ContinuousOn (fun u : ℝ => (u : ℂ) ^ w) (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) := by
      intro w
      have hce : ContinuousOn (fun u : ℝ => Complex.exp ((Real.log u : ℂ) * w))
          (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
        ContinuousOn.cexp ((Complex.continuous_ofReal.comp_continuousOn
          (Real.continuousOn_log.mono fun u hu => (lt_of_lt_of_le hm0 hu.1).ne')).mul continuousOn_const)
      refine hce.congr fun u hu => ?_
      have hu0 : 0 < u := lt_of_lt_of_le hm0 hu.1
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'), ← Complex.ofReal_log hu0.le]
    have hcont_q : Continuous (fun u : ℝ => ((q u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul
        ((((continuous_id.sub continuous_const).pow 2).sub (continuous_id.sub continuous_const)).add continuous_const))
    have hcont_q' : Continuous (fun u : ℝ => ((q' u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).sub continuous_const)
    have hcont_t1 : ContinuousOn (fun u : ℝ => ((q' u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
        (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
      hcont_q'.continuousOn.mul (hcont_pow (-s - 1))
    have hcont_t2 : ContinuousOn (fun u : ℝ => ((q u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
        (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
      hcont_q.continuousOn.mul (hcont_pow (-s - 2))
    have hcont_t2' : ContinuousOn (fun u : ℝ => (s + 1) * (((q u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)))
        (Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :=
      continuousOn_const.mul hcont_t2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hcont_t1.sub hcont_t2').intervalIntegrable_of_Icc hle)
    dsimp only [H'] at hftc
    rw [intervalIntegral.integral_sub (hcont_t1.intervalIntegrable_of_Icc hle)
      (hcont_t2'.intervalIntegrable_of_Icc hle),
      intervalIntegral.integral_const_mul] at hftc
    have hHm : H (m : ℝ) = (1 / 12 : ℂ) * (m : ℂ) ^ (-s - 1) := by
      dsimp only [H, q]; push_cast; ring
    have hHm1 : H ((m + 1 : ℕ) : ℝ) = (1 / 12 : ℂ) * ((m + 1 : ℕ) : ℂ) ^ (-s - 1) := by
      dsimp only [H, q]; push_cast; ring
    -- Replace `q'` by `fractNat - 1/2` and `q` by `periodB2` on `(m, m + 1)` (a.e. equal on `Ioc m (m + 1)`!)
    have hfl_eq : ∀ u ∈ Set.Ioo (m : ℝ) ((m + 1 : ℕ) : ℝ), ⌊u⌋₊ = m := by
      intro u hu
      exact Nat.floor_eq_iff (lt_of_lt_of_le hm0 hu.1.le).le |>.mpr ⟨hu.1.le, by push_cast at hu; exact hu.2⟩
    have hEq1 : ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ),
          (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) =
        ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((q' t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      dsimp only [Stage5ZetaZeroFree.fractNat, q']
      rw [hfl_eq u hu]
    have hEq2 : ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ),
          ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) =
        ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((q t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      dsimp only [periodB2, Stage5ZetaZeroFree.fractNat, q]
      rw [hfl_eq u hu]
    rw [hEq1, hEq2]
    rw [hHm, hHm1] at hftc
    linear_combination hftc
  -- Telescope `hunit` from `N` to `N + K` for every `K : ℕ`
  have htel : ∀ K : ℕ,
      ∫ t in (N : ℝ)..((N + K : ℕ) : ℝ),
        (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) =
      (1 / 12 : ℂ) * (((N + K : ℕ) : ℂ) ^ (-s - 1) - (N : ℂ) ^ (-s - 1)) +
        (s + 1) * ∫ t in (N : ℝ)..((N + K : ℕ) : ℝ),
          ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hle1 : (N : ℝ) ≤ ((N + K : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right N K)
      have hle2 : ((N + K : ℕ) : ℝ) ≤ ((N + (K + 1) : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
      have h1L : IntervalIntegrable
          (fun t : ℝ => (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)))
          volume (N : ℝ) ((N + K : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hle1).mpr
          (hint_lhs.mono_set Set.Ioc_subset_Ioi_self)
      have h2L : IntervalIntegrable
          (fun t : ℝ => (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)))
          volume ((N + K : ℕ) : ℝ) ((N + (K + 1) : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hle2).mpr
          (hint_lhs.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hle1)))
      have h1R : IntervalIntegrable
          (fun t : ℝ => ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2))
          volume (N : ℝ) ((N + K : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hle1).mpr
          (hint_rhs.mono_set Set.Ioc_subset_Ioi_self)
      have h2R : IntervalIntegrable
          (fun t : ℝ => ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2))
          volume ((N + K : ℕ) : ℝ) ((N + (K + 1) : ℕ) : ℝ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hle2).mpr
          (hint_rhs.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hle1)))
      rw [← intervalIntegral.integral_add_adjacent_intervals h1L h2L,
        ← intervalIntegral.integral_add_adjacent_intervals h1R h2R, ih]
      have hadd : (N + (K + 1) : ℕ) = (N + K) + 1 := by omega
      rw [hadd, hunit (N + K) (Nat.le_add_right N K)]
      ring
  -- Take `K → ∞`!
  have htop : Tendsto (fun K : ℕ => ((N + K : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono (fun K => Nat.cast_le.mpr (Nat.le_add_left K N)) h1
  have htendL := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_lhs htop
  have htendR_int := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_rhs htop
  have htend_pow : Tendsto (fun K : ℕ => (((N + K : ℕ) : ℂ) ^ (-s - 1))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ K : ℕ, ‖((N + K : ℕ) : ℂ) ^ (-s - 1)‖ = ((N + K : ℕ) : ℝ) ^ (-s.re - 1) := by
      intro K
      have hpos : (0 : ℝ) < ((N + K : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
    simp_rw [hnorm]
    exact ((tendsto_rpow_neg_atTop (by linarith : 0 < s.re + 1)).comp htop).congr fun K => by
      dsimp only [Function.comp_def]; rw [show -(s.re + 1) = -s.re - 1 by ring]
  have htendR : Tendsto (fun K : ℕ =>
      (1 / 12 : ℂ) * (((N + K : ℕ) : ℂ) ^ (-s - 1) - (N : ℂ) ^ (-s - 1)) +
        (s + 1) * ∫ t in (N : ℝ)..((N + K : ℕ) : ℝ),
          ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2))
      atTop (nhds (-(1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1) +
        (s + 1) * ∫ t in Ioi (N : ℝ), ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2))) := by
    have h1 := ((htend_pow.sub (tendsto_const_nhds (x := (N : ℂ) ^ (-s - 1)))).const_mul (1 / 12 : ℂ)).add
      (htendR_int.const_mul (s + 1))
    simpa [zero_sub, mul_neg, neg_mul] using h1
  have htendL' : Tendsto (fun K : ℕ =>
      (1 / 12 : ℂ) * (((N + K : ℕ) : ℂ) ^ (-s - 1) - (N : ℂ) ^ (-s - 1)) +
        (s + 1) * ∫ t in (N : ℝ)..((N + K : ℕ) : ℝ),
          ((periodB2 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 2))
      atTop (nhds (∫ t in Ioi (N : ℝ),
        (((Stage5ZetaZeroFree.fractNat t - 1 / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)))) :=
    htendL.congr htel
  exact tendsto_nhds_unique htendL' htendR

/-- Non-stationary phase IBP estimate for Fourier modes `k ≥ 1`, `ε ∈ {1, -1}`:
when `1 ≤ N`, `0 < σ`, `|t| ≤ N`,
`‖∫_N^∞ exp(I * ε * 2 * π * k * u) * u^(-(σ + I*t) - 2) du‖ ≤ (1 / k) * N^(-σ - 2)`. -/
lemma norm_integral_cexp_rpow_le {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {σ t ε : ℝ} (hσ : 0 < σ) (ht : |t| ≤ (N : ℝ)) (hε : |ε| = 1) :
    ‖∫ u in Ioi (N : ℝ),
        Complex.exp (Complex.I * ((ε * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) *
          (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 2)‖ ≤
      (1 / (k : ℝ)) * (N : ℝ) ^ (-σ - 2) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  let φ : ℝ → ℝ := fun u => ε * 2 * Real.pi * (k : ℝ) * u - t * Real.log u
  let φ' : ℝ → ℝ := fun u => ε * 2 * Real.pi * (k : ℝ) - t / u
  have hφ'_ge : ∀ u : ℝ, (N : ℝ) ≤ u → 5 * (k : ℝ) ≤ |φ' u| := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hN0 hu
    have htu : |t / u| ≤ 1 := by
      rw [abs_div, abs_of_pos hu0, div_le_one hu0]
      exact ht.trans hu
    have hmain : 6 * (k : ℝ) ≤ |ε * 2 * Real.pi * (k : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, hε, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos, abs_of_pos hk0]
      nlinarith
    have hrev : |ε * 2 * Real.pi * (k : ℝ)| - |t / u| ≤ |φ' u| := by
      dsimp only [φ']
      linarith [abs_sub_abs_le_abs_sub (ε * 2 * Real.pi * (k : ℝ)) (t / u)]
    linarith
  have hφ'_ne : ∀ u : ℝ, (N : ℝ) ≤ u → φ' u ≠ 0 := by
    intro u hu h0
    have h1 := hφ'_ge u hu
    rw [h0, abs_zero] at h1
    linarith
  -- Rewrite integrand as `cexp (I * φ u) * u^(-σ-2)`
  have hint_rew : ∀ u : ℝ, 0 < u →
      Complex.exp (Complex.I * ((ε * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) *
        (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 2) =
      Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ) := by
    intro u hu
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.le, Real.rpow_def_of_pos hu,
      Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; dsimp only [φ]; push_cast; ring
  let g : ℝ → ℂ := fun u => ((u ^ (-σ - 2) : ℝ) : ℂ) / (Complex.I * (φ' u : ℂ))
  let g' : ℝ → ℂ := fun u =>
    (((-σ - 2) * u ^ (-σ - 3) / φ' u - u ^ (-σ - 2) * (t / u ^ 2) / (φ' u) ^ 2 : ℝ) : ℂ) / Complex.I
  have hderiv : ∀ u : ℝ, (N : ℝ) ≤ u →
      HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (φ x : ℂ)) * g x)
        (Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ) +
         Complex.exp (Complex.I * (φ u : ℂ)) * g' u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hN0 hu
    have hφu_ne : φ' u ≠ 0 := hφ'_ne u hu
    have hφ_deriv : HasDerivAt φ (φ' u) u := by
      dsimp only [φ, φ']
      have h1 : HasDerivAt (fun x : ℝ => ε * 2 * Real.pi * (k : ℝ) * x) (ε * 2 * Real.pi * (k : ℝ)) u := by
        simpa using (hasDerivAt_id u).const_mul (ε * 2 * Real.pi * (k : ℝ))
      have h2 : HasDerivAt (fun x : ℝ => t * Real.log x) (t / u) u := by
        simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hu0.ne').const_mul t
      exact h1.sub h2
    have hexp_deriv : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (φ x : ℂ)))
        (Complex.exp (Complex.I * (φ u : ℂ)) * (Complex.I * (φ' u : ℂ))) u :=
      (hφ_deriv.ofReal_comp.const_mul Complex.I).cexp
    have hg_deriv : HasDerivAt g (g' u) u := by
      have hnum : HasDerivAt (fun x : ℝ => x ^ (-σ - 2)) ((-σ - 2) * u ^ (-σ - 3)) u := by
        have h := Real.hasDerivAt_rpow_const (p := -σ - 2) (Or.inl hu0.ne')
        refine h.congr_deriv ?_; congr 2; ring
      have hden : HasDerivAt φ' (t / u ^ 2) u := by
        dsimp only [φ']
        have hinv : HasDerivAt (fun x : ℝ => t / x) (-(t / u ^ 2)) u := by
          have h := (hasDerivAt_inv hu0.ne').const_mul t
          refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => by ring)).congr_deriv ?_
          ring
        have hsub := (hasDerivAt_const u (ε * 2 * Real.pi * (k : ℝ))).sub hinv
        refine hsub.congr_deriv ?_; ring
      have hdivR : HasDerivAt (fun x : ℝ => x ^ (-σ - 2) / φ' x)
          (((-σ - 2) * u ^ (-σ - 3) * φ' u - u ^ (-σ - 2) * (t / u ^ 2)) / (φ' u) ^ 2) u :=
        hnum.div hden hφu_ne
      have hdivC : HasDerivAt (fun x : ℝ => ((x ^ (-σ - 2) / φ' x : ℝ) : ℂ) / Complex.I) (g' u) u := by
        refine (hdivR.ofReal_comp.div_const Complex.I).congr_deriv ?_
        dsimp only [g']
        congr 1; congr 1
        field_simp [hφu_ne]
      refine hdivC.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      dsimp only [g]; push_cast; ring
    refine (hexp_deriv.mul hg_deriv).congr_deriv ?_
    dsimp only [g]
    have hφC : (φ' u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hφu_ne
    field_simp [Complex.I_ne_zero, hφC]
  -- Pointwise norm bound on `g' u` for `u ≥ N`: `‖g' u‖ ≤ ((σ + 3) / (5 * k)) * u^(-σ-3)`
  have hg'_bound : ∀ u : ℝ, (N : ℝ) ≤ u →
      ‖g' u‖ ≤ ((σ + 3) / (5 * (k : ℝ))) * u ^ (-σ - 3) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hN0 hu
    have hφge := hφ'_ge u hu
    have hφpos : 0 < |φ' u| := lt_of_lt_of_le (by positivity) hφge
    have htu : |t| / u ≤ 1 := (div_le_one hu0).mpr (ht.trans hu)
    dsimp only [g']
    rw [norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(-σ - 2) * u ^ (-σ - 3) / φ' u| ≤ ((σ + 2) / (5 * (k : ℝ))) * u ^ (-σ - 3) := by
      rw [abs_div, abs_mul, abs_of_neg (by linarith : -σ - 2 < 0),
        abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
      have hdiv : (-( -σ - 2)) * u ^ (-σ - 3) / |φ' u| ≤ (σ + 2) * u ^ (-σ - 3) / (5 * (k : ℝ)) := by
        rw [show -(-σ - 2) = σ + 2 by ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hφge
      linarith [show (σ + 2) * u ^ (-σ - 3) / (5 * (k : ℝ)) = ((σ + 2) / (5 * (k : ℝ))) * u ^ (-σ - 3) by ring]
    have h2 : |u ^ (-σ - 2) * (t / u ^ 2) / (φ' u) ^ 2| ≤ (1 / (5 * (k : ℝ))) * u ^ (-σ - 3) := by
      rw [abs_div, abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hu0 _),
        abs_of_pos (sq_pos_of_pos hu0), abs_pow]
      have hpow_eq : u ^ (-σ - 2) / u = u ^ (-σ - 3) := by
        rw [show u ^ (-σ - 2) / u = u ^ (-σ - 2) / u ^ (1 : ℝ) by rw [Real.rpow_one],
          ← Real.rpow_sub hu0]
        congr 1; ring
      have hnum : u ^ (-σ - 2) * (|t| / u ^ 2) ≤ u ^ (-σ - 3) := by
        have hrew : u ^ (-σ - 2) * (|t| / u ^ 2) = (|t| / u) * (u ^ (-σ - 2) / u) := by ring
        rw [hrew, hpow_eq]
        exact mul_le_of_le_one_left (Real.rpow_nonneg hu0.le _) htu
      have hden : 5 * (k : ℝ) ≤ |φ' u| ^ 2 := by
        have hsq : (5 * (k : ℝ)) ^ 2 ≤ |φ' u| ^ 2 := sq_le_sq' (by linarith) hφge
        nlinarith
      calc u ^ (-σ - 2) * (|t| / u ^ 2) / |φ' u| ^ 2
          ≤ u ^ (-σ - 3) / (5 * (k : ℝ)) :=
            div_le_div₀ (Real.rpow_nonneg hu0.le _) hnum (by positivity) hden
        _ = (1 / (5 * (k : ℝ))) * u ^ (-σ - 3) := by ring
    calc |(-σ - 2) * u ^ (-σ - 3) / φ' u - u ^ (-σ - 2) * (t / u ^ 2) / (φ' u) ^ 2|
        ≤ |(-σ - 2) * u ^ (-σ - 3) / φ' u| + |u ^ (-σ - 2) * (t / u ^ 2) / (φ' u) ^ 2| := abs_sub _ _
      _ ≤ ((σ + 2) / (5 * (k : ℝ))) * u ^ (-σ - 3) + (1 / (5 * (k : ℝ))) * u ^ (-σ - 3) :=
          add_le_add h1 h2
      _ = ((σ + 3) / (5 * (k : ℝ))) * u ^ (-σ - 3) := by ring
  -- Bound the integral on `[N, M]` for any `M ≥ N`, then let `M → ∞`!
  have hcont_orig : ContinuousOn
      (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ))
      (Ici (N : ℝ)) := by
    have hφ_cont : ContinuousOn φ (Ici (N : ℝ)) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.mul (Real.continuousOn_log.mono fun u hu => (lt_of_lt_of_le hN0 hu).ne'))
    have hrpow_cont : ContinuousOn (fun u : ℝ => u ^ (-σ - 2)) (Ici (N : ℝ)) :=
      continuousOn_id.rpow_const fun u hu => Or.inl (lt_of_lt_of_le hN0 hu).ne'
    exact (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ_cont))).mul
      (Complex.continuous_ofReal.comp_continuousOn hrpow_cont)
  have hcont_g' : ContinuousOn
      (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)) * g' u) (Ici (N : ℝ)) := by
    have hφ_cont : ContinuousOn φ (Ici (N : ℝ)) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.mul (Real.continuousOn_log.mono fun u hu => (lt_of_lt_of_le hN0 hu).ne'))
    have hφ'_cont : ContinuousOn φ' (Ici (N : ℝ)) :=
      continuousOn_const.sub (continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hN0 hu).ne')
    have hg'_cont : ContinuousOn g' (Ici (N : ℝ)) := by
      dsimp only [g']
      refine (Complex.continuous_ofReal.comp_continuousOn ?_).div_const Complex.I
      have h1 : ContinuousOn (fun u : ℝ => (-σ - 2) * u ^ (-σ - 3) / φ' u) (Ici (N : ℝ)) :=
        (continuousOn_const.mul (continuousOn_id.rpow_const fun u hu => Or.inl (lt_of_lt_of_le hN0 hu).ne')).div
          hφ'_cont (fun u hu => hφ'_ne u hu)
      have h2 : ContinuousOn (fun u : ℝ => u ^ (-σ - 2) * (t / u ^ 2) / (φ' u) ^ 2) (Ici (N : ℝ)) :=
        ((continuousOn_id.rpow_const fun u hu => Or.inl (lt_of_lt_of_le hN0 hu).ne').mul
          (continuousOn_const.div (continuousOn_id.pow 2) fun u hu => pow_ne_zero 2 (lt_of_lt_of_le hN0 hu).ne')).div
          (hφ'_cont.pow 2) (fun u hu => pow_ne_zero 2 (hφ'_ne u hu))
      exact h1.sub h2
    exact (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ_cont))).mul hg'_cont
  have hM_bound : ∀ M : ℝ, (N : ℝ) ≤ M →
      ‖∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ)‖ ≤
      (1 / (5 * (k : ℝ))) * M ^ (-σ - 2) + (3 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) := by
    intro M hNM
    have hsub : Set.uIcc (N : ℝ) M ⊆ Ici (N : ℝ) := by
      rw [Set.uIcc_of_le hNM]; exact fun u hu => hu.1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hderiv u (hsub hu))
      (((hcont_orig.add hcont_g').mono hsub).intervalIntegrable)
    rw [intervalIntegral.integral_add ((hcont_orig.mono hsub).intervalIntegrable)
      ((hcont_g'.mono hsub).intervalIntegrable)] at hftc
    have heq : ∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ) =
        Complex.exp (Complex.I * (φ M : ℂ)) * g M -
        Complex.exp (Complex.I * (φ (N : ℝ) : ℂ)) * g (N : ℝ) -
        ∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u := by
      linear_combination hftc
    rw [heq]
    have hnorm_exp : ∀ x : ℝ, ‖Complex.exp (Complex.I * (φ x : ℂ))‖ = 1 := fun x => by
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    have hnorm_g : ∀ x : ℝ, (N : ℝ) ≤ x → ‖g x‖ ≤ (1 / (5 * (k : ℝ))) * x ^ (-σ - 2) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hN0 hx
      dsimp only [g]
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), Real.norm_eq_abs]
      calc x ^ (-σ - 2) / |φ' x| ≤ x ^ (-σ - 2) / (5 * (k : ℝ)) :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (by positivity) (hφ'_ge x hx)
        _ = (1 / (5 * (k : ℝ))) * x ^ (-σ - 2) := by ring
    have hint_g' : ‖∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u‖ ≤
        (2 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) := by
      have h1 : ‖∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u‖ ≤
          ∫ u in (N : ℝ)..M, ((σ + 3) / (5 * (k : ℝ))) * u ^ (-σ - 3) := by
        refine (intervalIntegral.norm_integral_le_integral_norm hNM).trans ?_
        refine intervalIntegral.integral_mono_on hNM
          ((hcont_g'.mono hsub).norm.intervalIntegrable)
          ((continuousOn_const.mul (continuousOn_id.rpow_const fun u hu =>
            Or.inl (lt_of_lt_of_le hN0 (hsub hu)).ne')).intervalIntegrable) fun u hu => ?_
        rw [norm_mul, hnorm_exp u, one_mul]
        exact hg'_bound u hu.1
      have h2 : ∫ u in (N : ℝ)..M, ((σ + 3) / (5 * (k : ℝ))) * u ^ (-σ - 3) ≤
          ((σ + 3) / (5 * (k : ℝ))) * ((N : ℝ) ^ (-σ - 2) / (σ + 2)) := by
        rw [intervalIntegral.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hint_dom : IntegrableOn (fun u : ℝ => u ^ (-σ - 3)) (Ioi (N : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt (by linarith) hN0
        rw [intervalIntegral.integral_of_le hNM]
        have hval : ∫ u in Ioi (N : ℝ), u ^ (-σ - 3) = (N : ℝ) ^ (-σ - 2) / (σ + 2) := by
          rw [integral_Ioi_rpow_of_lt (by linarith) hN0]
          have hadd : -σ - 3 + 1 = -σ - 2 := by ring
          rw [hadd]
          field_simp [(by linarith : -σ - 2 ≠ 0), (by linarith : σ + 2 ≠ 0)]
          ring
        rw [← hval]
        exact setIntegral_mono_set hint_dom
          ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => Real.rpow_nonneg (hN0.trans hu).le _)
          (Eventually.of_forall Set.Ioc_subset_Ioi_self)
      have hratio : (σ + 3) / (σ + 2) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have h3 : ((σ + 3) / (5 * (k : ℝ))) * ((N : ℝ) ^ (-σ - 2) / (σ + 2)) ≤
          (2 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) := by
        have hrew : ((σ + 3) / (5 * (k : ℝ))) * ((N : ℝ) ^ (-σ - 2) / (σ + 2)) =
            ((σ + 3) / (σ + 2)) * ((1 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2)) := by ring
        rw [hrew]
        have hmul := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ (1 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2))
        have h2eq : 2 * (1 / (5 * (k : ℝ)) * (N : ℝ) ^ (-σ - 2)) = (2 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) := by ring
        linarith
      exact h1.trans (h2.trans h3)
    have htri : ‖Complex.exp (Complex.I * (φ M : ℂ)) * g M -
        Complex.exp (Complex.I * (φ (N : ℝ) : ℂ)) * g (N : ℝ) -
        ∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u‖ ≤
        ‖g M‖ + ‖g (N : ℝ)‖ + ‖∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u‖ := by
      have h1 := norm_sub_le
        (Complex.exp (Complex.I * (φ M : ℂ)) * g M - Complex.exp (Complex.I * (φ (N : ℝ) : ℂ)) * g (N : ℝ))
        (∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * g' u)
      have h2 := norm_sub_le (Complex.exp (Complex.I * (φ M : ℂ)) * g M)
        (Complex.exp (Complex.I * (φ (N : ℝ) : ℂ)) * g (N : ℝ))
      rw [norm_mul, hnorm_exp, one_mul, norm_mul, hnorm_exp, one_mul] at h2
      linarith
    have h3eq : (1 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) + (2 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) =
        (3 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) := by ring
    linarith [hnorm_g M hNM, hnorm_g (N : ℝ) le_rfl, hint_g']
  -- Pass `M → ∞`!
  have hint_Ioi : IntegrableOn
      (fun u : ℝ => Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ))
      (Ioi (N : ℝ)) := by
    have hdom : IntegrableOn (fun u : ℝ => u ^ (-σ - 2)) (Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hN0
    refine hdom.mono' ((hcont_orig.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu0 : 0 < u := hN0.trans hu
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _)]
  have hcongr_Ioi : ∫ u in Ioi (N : ℝ),
        Complex.exp (Complex.I * ((ε * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) *
          (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 2) =
      ∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => hint_rew u (hN0.trans hu)
  rw [hcongr_Ioi]
  have htend_norm : Tendsto (fun M : ℝ =>
      ‖∫ u in (N : ℝ)..M, Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ)‖)
      atTop (nhds ‖∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ)‖) :=
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_Ioi tendsto_id).norm
  have htend_rhs : Tendsto (fun M : ℝ =>
      (1 / (5 * (k : ℝ))) * M ^ (-σ - 2) + (3 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2))
      atTop (nhds ((3 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2))) := by
    have h0 : Tendsto (fun M : ℝ => M ^ (-σ - 2)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < σ + 2)).congr fun M => by congr 1; ring
    simpa using ((h0.const_mul (1 / (5 * (k : ℝ)))).add tendsto_const_nhds)
  have hle_lim : ‖∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * (φ u : ℂ)) * ((u ^ (-σ - 2) : ℝ) : ℂ)‖ ≤
      (3 / (5 * (k : ℝ))) * (N : ℝ) ^ (-σ - 2) :=
    le_of_tendsto_of_tendsto htend_norm htend_rhs (eventually_atTop.mpr ⟨(N : ℝ), hM_bound⟩)
  have h35 : (3 / (5 * (k : ℝ))) ≤ 1 / (k : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hk0]; linarith
  exact hle_lim.trans (mul_le_mul_of_nonneg_right h35 (Real.rpow_nonneg hN0.le _))

/-- **Hardy–Littlewood / Titchmarsh Theorem 4.11 (Uniform Truncated Euler–Maclaurin Formula)**:
for every `σ t : ℝ` with `0 < σ`, `s = σ + I * t ≠ 1`, and every `N : ℕ` with `1 ≤ N`, `|t| ≤ N`,
and `σ ≤ N`,
`‖riemannZeta s - dirichletPoly (fun n => (n : ℂ)^(-(σ:ℂ))) N (I * t) - N^(1 - s) / (s - 1)‖ ≤ 2 * N^(-σ)`. -/
theorem riemannZeta_approx_eulerMaclaurin {N : ℕ} (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ)
    (hs1 : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1) (htN : |t| ≤ (N : ℝ)) (hσN : σ ≤ (N : ℝ)) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) -
      dirichletPoly (fun n => (n : ℂ) ^ (-(σ : ℂ))) N (Complex.I * (t : ℂ)) -
      (N : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) /
        (((σ : ℂ) + Complex.I * (t : ℂ)) - 1)‖ ≤ 2 * (N : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs_pos : 0 < s.re := by rw [hs_re]; exact hσ
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  -- Match `dirichletPoly` with `∑_{n=1}^N n^(-s)`
  have hdp : dirichletPoly (fun n => (n : ℂ) ^ (-(σ : ℂ))) N (Complex.I * (t : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    dsimp only [dirichletPoly]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
    rw [← Complex.cpow_add _ _ hnC]
    congr 1; dsimp only [s]; ring
  rw [hdp, Stage5ZetaZeroFree.riemannZeta_eq_eulerMaclaurin_trunc hN hs_pos hs1]
  have hsimp_diff :
      ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) -
        s * ∫ u in Ioi (N : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) -
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1) =
      -(s * ∫ u in Ioi (N : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
    ring
  rw [hsimp_diff, norm_neg]
  -- Split `{u} = 1/2 + ({u} - 1/2)`!
  have hint_half : IntegrableOn (fun u : ℝ => ((1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
    have hdom : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-σ - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul (1 / 2 : ℝ)
    refine hdom.mono' ((continuousOn_const.mul (continuousOn_ofReal_cpow_Ioi hN0 (-s - 1))).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu0 : 0 < u := hN0.trans hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
      Complex.norm_cpow_eq_rpow_re_of_pos hu0, show (-s - 1).re = -σ - 1 by simp [s]]
  have hint_sub : IntegrableOn
      (fun u : ℝ => (((Stage5ZetaZeroFree.fractNat u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)))
      (Ioi (N : ℝ)) := by
    have hdom : IntegrableOn (fun u : ℝ => u ^ (-σ - 1)) (Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hN0
    refine hdom.mono' ((Complex.measurable_ofReal.comp
      (Stage5ZetaZeroFree.measurable_fractNat.sub measurable_const)).aestronglyMeasurable.mul
      ((continuousOn_ofReal_cpow_Ioi hN0 (-s - 1)).aestronglyMeasurable measurableSet_Ioi)) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu0 : 0 < u := hN0.trans hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0, show (-s - 1).re = -σ - 1 by simp [s]]
    have hfr : |Stage5ZetaZeroFree.fractNat u - 1 / 2| ≤ 1 := by
      rw [abs_le]; constructor <;>
        linarith [Stage5ZetaZeroFree.fractNat_nonneg hu0.le, Stage5ZetaZeroFree.fractNat_lt_one u]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hu0.le _) hfr
  have hval_half : s * ∫ u in Ioi (N : ℝ), ((1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      (1 / 2 : ℂ) * (N : ℂ) ^ (-s) := by
    have h1 : ∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-s - 1) = (N : ℂ) ^ (-s) / s := by
      have hs0 : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
      have hint_p : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
        IntegrableOn.congr_fun (hint_half.const_mul (2 : ℂ)) (fun u _ => by push_cast; ring) measurableSet_Ioi
      have hftc_M : ∀ M : ℝ, (N : ℝ) ≤ M →
          ∫ u in (N : ℝ)..M, (u : ℂ) ^ (-s - 1) = ((N : ℂ) ^ (-s) - (M : ℂ) ^ (-s)) / s := by
        intro M hNM
        have hderiv : ∀ u ∈ Set.uIcc (N : ℝ) M,
            HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (-s)) / s) ((u : ℂ) ^ (-s - 1)) u := by
          intro u hu
          rw [Set.uIcc_of_le hNM] at hu
          have hu0 : 0 < u := lt_of_lt_of_le hN0 hu.1
          have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
          have hfun : (fun x : ℝ => (x : ℂ) ^ (-s)) =ᶠ[𝓝 u]
              fun x : ℝ => Complex.exp ((Real.log x : ℂ) * (-s)) := by
            filter_upwards [isOpen_Ioi.mem_nhds hu0] with x hx
            rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
              Complex.ofReal_log hx.le]
          have h1' : HasDerivAt (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * (-s)))
              (Complex.exp ((Real.log u : ℂ) * (-s)) * (((u⁻¹ : ℝ) : ℂ) * (-s))) u :=
            (((Real.hasDerivAt_log hu0.ne').ofReal_comp).mul_const (-s)).cexp
          refine ((h1'.congr_of_eventuallyEq hfun).neg.div_const s).congr_deriv ?_
          have hcp : Complex.exp ((Real.log u : ℂ) * (-s)) = (u : ℂ) ^ (-s) := by
            rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu0.le]
          have hsub : (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) / (u : ℂ) := by
            rw [Complex.cpow_sub _ _ huC, Complex.cpow_one]
          rw [hcp, hsub]; push_cast; field_simp [huC, hs0]
        have hcont : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) volume (N : ℝ) M :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hNM).mpr
            (hint_p.mono_set Set.Ioc_subset_Ioi_self)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
        push_cast; ring
      have ht1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint_p tendsto_id
      have ht2 : Tendsto (fun M : ℝ => ((N : ℂ) ^ (-s) - (M : ℂ) ^ (-s)) / s)
          atTop (nhds ((N : ℂ) ^ (-s) / s)) := by
        have hM0 : Tendsto (fun M : ℝ => (M : ℂ) ^ (-s)) atTop (nhds 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine (tendsto_rpow_neg_atTop hσ).congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hM, show (-s).re = -σ by simp [s]]
        simpa using (tendsto_const_nhds.sub hM0).div_const s
      exact tendsto_nhds_unique (ht1.congr' (eventually_atTop.mpr ⟨(N : ℝ), hftc_M⟩)) ht2
    rw [MeasureTheory.integral_const_mul, h1]
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs_pos; simp at hs_pos
    push_cast; field_simp [hs0]
  have hsplit_int :
      s * ∫ u in Ioi (N : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      (1 / 2 : ℂ) * (N : ℂ) ^ (-s) - (1 / 12 : ℂ) * s * (N : ℂ) ^ (-s - 1) +
        s * (s + 1) * ∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) := by
    have hpt : (fun u : ℝ => ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) =
        fun u : ℝ => ((1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) +
          (((Stage5ZetaZeroFree.fractNat u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      funext u; push_cast; ring
    rw [hpt, MeasureTheory.integral_add hint_half hint_sub, mul_add, hval_half,
      integral_fractNat_sub_half_ibp hN hs_pos]
    ring
  rw [hsplit_int]
  -- Bound `‖∫_N^∞ periodB2(u) * u^(-s-2) du‖ ≤ (1 / 12) * N^(-σ-2)` via Fourier series + `norm_integral_cexp_rpow_le`!
  have hP2_int_bound :
      ‖∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)‖ ≤
      (1 / 12 : ℝ) * (N : ℝ) ^ (-σ - 2) := by
    let F : ℕ → ℝ → ℂ := fun k u =>
      (((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * Real.cos (2 * Real.pi * (k : ℝ) * u) : ℝ) : ℂ) *
        (u : ℂ) ^ (-s - 2)
    have hF_sum : ∀ u ∈ Ioi (N : ℝ),
        HasSum (fun k : ℕ => F k u) (((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) := by
      intro u hu
      have hu0 : 0 ≤ u := (hN0.trans hu).le
      have h1 := (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hasSum_periodB2_fourier hu0))
      -- Use `HasSum.ofReal` + `HasSum.mul_right`
      have h2 : HasSum (fun k : ℕ =>
          (((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * Real.cos (2 * Real.pi * (k : ℝ) * u) : ℝ) : ℂ))
          ((periodB2 u : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr (hasSum_periodB2_fourier hu0)
      exact h2.mul_right ((u : ℂ) ^ (-s - 2))
    have hF_int : ∀ k : ℕ, IntegrableOn (F k) (Ioi (N : ℝ)) := by
      intro k
      have hdom : IntegrableOn (fun u : ℝ => (1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * u ^ (-σ - 2))
          (Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
      refine hdom.mono' ?_ ?_
      · refine ((Complex.measurable_ofReal.comp
          (measurable_const.mul (Real.continuous_cos.measurable.comp
            (measurable_const.mul measurable_id)))).aestronglyMeasurable.mul
          ((continuousOn_ofReal_cpow_Ioi hN0 (-s - 2)).aestronglyMeasurable measurableSet_Ioi))
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
        have hu0 : 0 < u := hN0.trans hu
        dsimp only [F]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)),
          Complex.norm_cpow_eq_rpow_re_of_pos hu0, show (-s - 2).re = -σ - 2 by simp [s]]
        have hcos : |Real.cos (2 * Real.pi * (k : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
        calc 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * |Real.cos (2 * Real.pi * (k : ℝ) * u)| * u ^ (-σ - 2)
            ≤ 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * 1 * u ^ (-σ - 2) := by
              gcongr
          _ = 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * u ^ (-σ - 2) := by ring
    have hF_norm_summable : Summable (fun k : ℕ => ∫ u in Ioi (N : ℝ), ‖F k u‖) := by
      have hdom_sum : Summable (fun k : ℕ =>
          ((N : ℝ) ^ (-σ - 1) / ((σ + 1) * (2 * Real.pi ^ 2))) * ((1 : ℝ) / (k : ℝ) ^ 2)) :=
        hasSum_zeta_two.summable.mul_left _
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) hdom_sum
      have hval : ∫ u in Ioi (N : ℝ), (1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)) * u ^ (-σ - 2) =
          ((N : ℝ) ^ (-σ - 1) / ((σ + 1) * (2 * Real.pi ^ 2))) * ((1 : ℝ) / (k : ℝ) ^ 2) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0,
          show -σ - 2 + 1 = -σ - 1 by ring]
        by_cases hk0 : k = 0
        · subst hk0; simp
        · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
          field_simp [(by linarith : -σ - 1 ≠ 0), (by linarith : σ + 1 ≠ 0), Real.pi_ne_zero, hkR]
          ring
      rw [← hval]
      refine setIntegral_mono_on (hF_int k).norm
        ((integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _) measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := hN0.trans hu
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2)),
        Complex.norm_cpow_eq_rpow_re_of_pos hu0, show (-s - 2).re = -σ - 2 by simp [s]]
      have hcos : |Real.cos (2 * Real.pi * (k : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
      calc 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * |Real.cos (2 * Real.pi * (k : ℝ) * u)| * u ^ (-σ - 2)
          ≤ 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * 1 * u ^ (-σ - 2) := by gcongr
        _ = 1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) * u ^ (-σ - 2) := by ring
    -- Apply `MeasureTheory.integral_tsum_of_summable_integral_norm`!
    have htsum_eq : ∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) =
        ∑' k : ℕ, ∫ u in Ioi (N : ℝ), F k u := by
      have hpt_eq : ∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) =
          ∫ u in Ioi (N : ℝ), ∑' k : ℕ, F k u :=
        setIntegral_congr_fun measurableSet_Ioi fun u hu => (hF_sum u hu).tsum_eq.symm
      rw [hpt_eq]
      exact (MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_norm_summable).symm
    rw [htsum_eq]
    -- Bound each term `‖∫_N^∞ F k u du‖ ≤ (1 / (2 * π^2 * k^2)) * N^(-σ-2)`
    have hterm_bd : ∀ k : ℕ,
        ‖∫ u in Ioi (N : ℝ), F k u‖ ≤ (1 / (2 * Real.pi ^ 2)) * ((1 : ℝ) / (k : ℝ) ^ 2) * (N : ℝ) ^ (-σ - 2) := by
      intro k
      by_cases hk0 : k = 0
      · subst hk0
        have hzero : F 0 = 0 := by funext u; simp [F]
        simp [hzero]
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have hcos_eq : ∀ u : ℝ,
            F k u = ((1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
              (Complex.exp (Complex.I * ((1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2) +
               Complex.exp (Complex.I * ((-1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2)) := by
          intro u
          dsimp only [F]
          rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
          have h1 : Complex.exp (↑(2 * Real.pi * (k : ℝ) * u) * Complex.I) =
              Complex.exp (Complex.I * ((1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) := by
            congr 1; push_cast; ring
          have h2 : Complex.exp (-↑(2 * Real.pi * (k : ℝ) * u) * Complex.I) =
              Complex.exp (Complex.I * ((-1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) := by
            congr 1; push_cast; ring
          rw [h1, h2]; push_cast; ring
        have hint_eps : ∀ ε : ℝ, IntegrableOn
            (fun u : ℝ => Complex.exp (Complex.I * ((ε * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2))
            (Ioi (N : ℝ)) := by
          intro ε
          refine (integrableOn_Ioi_rpow_of_lt (by linarith : -σ - 2 < -1) hN0).mono' ?_ ?_
          · exact ((Complex.continuous_exp.comp (continuous_const.mul
              (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))).measurable.aestronglyMeasurable.mul
              ((continuousOn_ofReal_cpow_Ioi hN0 (-s - 2)).aestronglyMeasurable measurableSet_Ioi))
          · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
            have hu0 : 0 < u := hN0.trans hu
            rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
              Complex.norm_cpow_eq_rpow_re_of_pos hu0, show (-s - 2).re = -σ - 2 by simp [s]]
        have hrew : ∫ u in Ioi (N : ℝ), F k u =
            ((1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
              ((∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * ((1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2)) +
               (∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * ((-1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2))) := by
          have hfn : F k = _ := funext hcos_eq
          rw [hfn, MeasureTheory.integral_const_mul, MeasureTheory.integral_add (hint_eps 1) (hint_eps (-1))]
        rw [hrew, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hp := norm_integral_cexp_rpow_le hN hk1 hσ htN (by norm_num : |(1 : ℝ)| = 1)
        have hm := norm_integral_cexp_rpow_le hN hk1 hσ htN (by norm_num : |(-1 : ℝ)| = 1)
        have hk_ge1 : (1 : ℝ) / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (Nat.one_le_cast.mpr hk1) (by positivity)
        calc 1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) *
              ‖(∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * ((1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2)) +
               (∫ u in Ioi (N : ℝ), Complex.exp (Complex.I * ((-1 * 2 * Real.pi * (k : ℝ) * u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 2))‖
            ≤ 1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) *
              ((1 / (k : ℝ)) * (N : ℝ) ^ (-σ - 2) + (1 / (k : ℝ)) * (N : ℝ) ^ (-σ - 2)) := by
              refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hp hm)) (by positivity)
          _ ≤ 1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2) * (2 * (N : ℝ) ^ (-σ - 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have := mul_le_mul_of_nonneg_right hk_ge1 (Real.rpow_nonneg hN0.le (-σ - 2))
              linarith
          _ = (1 / (2 * Real.pi ^ 2)) * ((1 : ℝ) / (k : ℝ) ^ 2) * (N : ℝ) ^ (-σ - 2) := by ring
    have hsum_bd : Summable (fun k : ℕ =>
        (1 / (2 * Real.pi ^ 2)) * ((1 : ℝ) / (k : ℝ) ^ 2) * (N : ℝ) ^ (-σ - 2)) :=
      (hasSum_zeta_two.summable.mul_left _).mul_right _
    have htsum_bd : ∑' k : ℕ, (1 / (2 * Real.pi ^ 2)) * ((1 : ℝ) / (k : ℝ) ^ 2) * (N : ℝ) ^ (-σ - 2) =
        (1 / 12 : ℝ) * (N : ℝ) ^ (-σ - 2) := by
      rw [tsum_mul_right, tsum_mul_left, hasSum_zeta_two.tsum_eq]
      field_simp [Real.pi_ne_zero]; ring
    have hnorm_tsum : ‖∑' k : ℕ, ∫ u in Ioi (N : ℝ), F k u‖ ≤
        ∑' k : ℕ, ‖∫ u in Ioi (N : ℝ), F k u‖ :=
      norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd hsum_bd)
    exact hnorm_tsum.trans ((Summable.tsum_le_tsum hterm_bd
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd hsum_bd) hsum_bd).trans_eq htsum_bd)
  -- Assemble the 3 pieces: `(1/2 + 1/6 + 1/2) * N^(-σ) ≤ 2 * N^(-σ)`!
  have hs_norm : ‖s‖ ≤ 2 * (N : ℝ) := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = σ + |t| := by rw [hs_re, abs_of_pos hσ]; simp [s]
      _ ≤ (N : ℝ) + (N : ℝ) := add_le_add hσN htN
      _ = 2 * (N : ℝ) := by ring
  have hs1_norm : ‖s + 1‖ ≤ 3 * (N : ℝ) := by
    calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * (N : ℝ) + 1 := by rw [norm_one]; linarith
      _ ≤ 3 * (N : ℝ) := by linarith
  have hNpow1 : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-σ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, show (-s).re = -σ by simp [s]]
  have hNpow2 : ‖(N : ℂ) ^ (-s - 1)‖ = (N : ℝ) ^ (-σ - 1) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, show (-s - 1).re = -σ - 1 by simp [s]]
  have hNp1 : (N : ℝ) * (N : ℝ) ^ (-σ - 1) = (N : ℝ) ^ (-σ) := by
    rw [show (N : ℝ) * (N : ℝ) ^ (-σ - 1) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-σ - 1) by rw [Real.rpow_one],
      ← Real.rpow_add hN0]; congr 1; ring
  have hNp2 : (N : ℝ) ^ 2 * (N : ℝ) ^ (-σ - 2) = (N : ℝ) ^ (-σ) := by
    rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hN0]; congr 1; ring
  have htri1 := norm_add_le ((1 / 2 : ℂ) * (N : ℂ) ^ (-s) - (1 / 12 : ℂ) * s * (N : ℂ) ^ (-s - 1))
    (s * (s + 1) * ∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
  have htri2 := norm_sub_le ((1 / 2 : ℂ) * (N : ℂ) ^ (-s)) ((1 / 12 : ℂ) * s * (N : ℂ) ^ (-s - 1))
  have hP1 : ‖(1 / 2 : ℂ) * (N : ℂ) ^ (-s)‖ = (1 / 2 : ℝ) * (N : ℝ) ^ (-σ) := by
    rw [norm_mul, hNpow1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hP2 : ‖(1 / 12 : ℂ) * s * (N : ℂ) ^ (-s - 1)‖ ≤ (1 / 6 : ℝ) * (N : ℝ) ^ (-σ) := by
    rw [norm_mul, norm_mul, hNpow2, show (1 / 12 : ℂ) = ((1 / 12 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    calc (1 / 12 : ℝ) * ‖s‖ * (N : ℝ) ^ (-σ - 1)
        ≤ (1 / 12 : ℝ) * (2 * (N : ℝ)) * (N : ℝ) ^ (-σ - 1) := by gcongr
      _ = (1 / 6 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-σ - 1)) := by ring
      _ = (1 / 6 : ℝ) * (N : ℝ) ^ (-σ) := by rw [hNp1]
  have hP3 : ‖s * (s + 1) * ∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)‖ ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ (-σ) := by
    rw [norm_mul, norm_mul]
    calc ‖s‖ * ‖s + 1‖ * ‖∫ u in Ioi (N : ℝ), ((periodB2 u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)‖
        ≤ (2 * (N : ℝ)) * (3 * (N : ℝ)) * ((1 / 12 : ℝ) * (N : ℝ) ^ (-σ - 2)) := by
          gcongr
      _ = (1 / 2 : ℝ) * ((N : ℝ) ^ 2 * (N : ℝ) ^ (-σ - 2)) := by ring
      _ = (1 / 2 : ℝ) * (N : ℝ) ^ (-σ) := by rw [hNp2]
  have hposN : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hN0.le _
  linarith

/-- Helper: `(riemannZeta (2 * (σ : ℂ))).re = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 * σ)` for `1 / 2 < σ`. -/
lemma riemannZeta_two_mul_re_eq_tsum {σ : ℝ} (hσ : 1 / 2 < σ) :
    (riemannZeta (2 * (σ : ℂ))).re = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) := by
  have hre : 1 < (2 * (σ : ℂ)).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * (σ : ℂ)) =
      ((((n + 1 : ℕ) : ℝ) ^ (-2 * σ) : ℝ) : ℂ) := by
    intro n
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      show (2 * (σ : ℂ)) = ((2 * σ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le, ← Complex.ofReal_one, ← Complex.ofReal_div,
      one_div, ← Real.rpow_neg hpos.le]
    congr 2; ring
  simp_rw [hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- Helper: `∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) → (riemannZeta (2 * (σ : ℂ))).re` as `N → ∞`. -/
lemma tendsto_sum_rpow_neg_two_mul {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ))
      atTop (nhds ((riemannZeta (2 * (σ : ℂ))).re)) := by
  rw [riemannZeta_two_mul_re_eq_tsum hσ]
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * σ)) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * σ)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * σ)) :=
      (summable_nat_add_iff 1).mpr h1
    refine h2.congr fun n => ?_
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg _), show -(2 * σ) = -2 * σ by ring]
  have hrange := hsum.hasSum.tendsto_sum_nat
  refine hrange.congr fun N => ?_
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
  · intro a _ b _ h; omega
  · intro n hn; rw [Finset.mem_Icc] at hn; exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _; rfl

/-- Helper: uniform sublinear bound for `∑_{n=1}^N n^(1 - 2 * σ) = o(N)` for every `σ > 1 / 2`. -/
lemma sum_rpow_one_sub_two_mul_div_tendsto_zero {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun T : ℝ => (1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ))
      atTop (nhds 0) := by
  set δ : ℝ := min (σ - 1 / 2) (1 / 4)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le1 : 2 * δ ≤ 2 * σ - 1 := by
    have : δ ≤ σ - 1 / 2 := min_le_left _ _; linarith
  have hδ_le2 : 2 * δ ≤ 1 / 2 := by
    have : δ ≤ 1 / 4 := min_le_right _ _; linarith
  -- Bound `∑_{n=1}^N n^(1 - 2σ) ≤ ∑_{n=1}^N n^(-2δ) ≤ 1 + N^(1 - 2δ) / (1 - 2δ)`
  have hN_bd : ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) ≤
        1 + (N : ℝ) ^ (1 - 2 * δ) / (1 - 2 * δ) := by
    intro N hN
    have h1 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) ≤
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * δ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Finset.mem_Icc.mp hn).1) (by linarith)
    refine h1.trans ?_
    -- Split `n = 1` and `2 ≤ n ≤ N`, compare `n^(-2δ) ≤ ∫_{n-1}^n x^(-2δ) dx`
    have hsplit : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * δ) =
        1 + ∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-2 * δ) := by
      have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp), Nat.cast_one, Real.one_rpow]
    rw [hsplit]
    have hstep : ∀ n : ℕ, 2 ≤ n →
        (n : ℝ) ^ (-2 * δ) ≤
          ((n : ℝ) ^ (1 - 2 * δ) - ((n - 1 : ℕ) : ℝ) ^ (1 - 2 * δ)) / (1 - 2 * δ) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
      have hn0 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
      have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
      have hftc : ∫ x in ((n - 1 : ℕ) : ℝ)..(n : ℝ), x ^ (-2 * δ) =
          ((n : ℝ) ^ (1 - 2 * δ) - ((n - 1 : ℕ) : ℝ) ^ (1 - 2 * δ)) / (1 - 2 * δ) := by
        have hd : ∀ x ∈ Set.uIcc ((n - 1 : ℕ) : ℝ) (n : ℝ),
            HasDerivAt (fun u : ℝ => u ^ (1 - 2 * δ) / (1 - 2 * δ)) (x ^ (-2 * δ)) x := by
          intro x hx
          rw [Set.uIcc_of_le hle] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
          have h := (Real.hasDerivAt_rpow_const (p := 1 - 2 * δ) (Or.inl hx0.ne')).div_const (1 - 2 * δ)
          refine h.congr_deriv ?_
          rw [show 1 - 2 * δ - 1 = -2 * δ by ring]
          field_simp [(by linarith : 1 - 2 * δ ≠ 0)]
        have hc : ContinuousOn (fun u : ℝ => u ^ (-2 * δ)) (Set.uIcc ((n - 1 : ℕ) : ℝ) (n : ℝ)) :=
          continuousOn_id.rpow_const fun x hx => by
            rw [Set.uIcc_of_le hle] at hx; exact Or.inl (lt_of_lt_of_le hn0 hx.1).ne'
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
        ring
      rw [← hftc]
      have hmono : ∫ _ in ((n - 1 : ℕ) : ℝ)..(n : ℝ), (n : ℝ) ^ (-2 * δ) ≤
          ∫ x in ((n - 1 : ℕ) : ℝ)..(n : ℝ), x ^ (-2 * δ) := by
        refine intervalIntegral.integral_mono_on hle intervalIntegrable_const ?_ fun x hx => ?_
        · exact (continuousOn_id.rpow_const fun u hu => Or.inl (lt_of_lt_of_le hn0 hu.1).ne').intervalIntegrable_of_Icc hle
        · exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hn0 hx.1) hx.2 (by linarith)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have hdiff : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
        have hcast : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) := Nat.cast_inj.mpr (by omega)
        push_cast at hcast; linarith
      rw [hdiff, one_mul] at hmono
      exact hmono
    have htel : ∀ r : ℕ,
        ∑ n ∈ Finset.Icc 2 (r + 1),
          ((n : ℝ) ^ (1 - 2 * δ) - ((n - 1 : ℕ) : ℝ) ^ (1 - 2 * δ)) / (1 - 2 * δ) =
        (((r + 1 : ℕ) : ℝ) ^ (1 - 2 * δ) - 1) / (1 - 2 * δ) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        have hIcc : Finset.Icc 2 (r + 2) = insert (r + 2) (Finset.Icc 2 (r + 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        have hsub : (r + 2 - 1 : ℕ) = r + 1 := by omega
        rw [hsub]; ring
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
    have hsum_le : ∑ n ∈ Finset.Icc 2 (r + 1), (n : ℝ) ^ (-2 * δ) ≤
        (((r + 1 : ℕ) : ℝ) ^ (1 - 2 * δ) - 1) / (1 - 2 * δ) :=
      (Finset.sum_le_sum fun n hn => hstep n (Finset.mem_Icc.mp hn).1).trans_eq (htel r)
    rw [Nat.add_comm 1 r] at hsplit ⊢
    have hsub1 : ((((r + 1 : ℕ) : ℝ) ^ (1 - 2 * δ) - 1) / (1 - 2 * δ)) ≤
        ((r + 1 : ℕ) : ℝ) ^ (1 - 2 * δ) / (1 - 2 * δ) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  -- Squeeze `(1 / T) * (1 + (T + 1)^(1 - 2δ) / (1 - 2δ)) → 0`
  have hupper : Tendsto (fun T : ℝ => (1 / T) * (1 + (T + 1) ^ (1 - 2 * δ) / (1 - 2 * δ)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 / T) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun T : ℝ => (1 / (1 - 2 * δ)) * ((1 + 1 / T) ^ (1 - 2 * δ) * T ^ (-2 * δ)))
        atTop (nhds 0) := by
      have ha : Tendsto (fun T : ℝ => (1 + 1 / T) ^ (1 - 2 * δ)) atTop (nhds ((1 + 0) ^ (1 - 2 * δ))) :=
        (tendsto_const_nhds.add h1).rpow_const (Or.inl (by norm_num))
      have hb : Tendsto (fun T : ℝ => T ^ (-2 * δ)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * δ)).congr fun T => by congr 1; ring
      simpa using (ha.mul hb).const_mul (1 / (1 - 2 * δ))
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTp1 : T + 1 = T * (1 + 1 / T) := by field_simp [hT.ne']
    have hdivT : T ^ (1 - 2 * δ) / T = T ^ (-2 * δ) := by
      rw [show T ^ (1 - 2 * δ) / T = T ^ (1 - 2 * δ) / T ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_sub hT]
      congr 1; ring
    rw [hTp1, Real.mul_rpow hT.le (by positivity),
      show (1 / T) * (1 + T ^ (1 - 2 * δ) * (1 + 1 / T) ^ (1 - 2 * δ) / (1 - 2 * δ)) =
        1 / T + (1 / (1 - 2 * δ)) * ((1 + 1 / T) ^ (1 - 2 * δ) * (T ^ (1 - 2 * δ) / T)) by ring,
      hdivT]
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hceil1 : 1 ≤ ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (by intro h; have := Nat.le_ceil T; rw [h] at this; simp at this; linarith)
    have hceil_le : (⌈T⌉₊ : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have hbd := hN_bd ⌈T⌉₊ hceil1
    have hrpow_le : (⌈T⌉₊ : ℝ) ^ (1 - 2 * δ) ≤ (T + 1) ^ (1 - 2 * δ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hceil_le (by linarith)
    have hdiv : (⌈T⌉₊ : ℝ) ^ (1 - 2 * δ) / (1 - 2 * δ) ≤ (T + 1) ^ (1 - 2 * δ) / (1 - 2 * δ) :=
      div_le_div_of_nonneg_right hrpow_le (by linarith)
    refine mul_le_mul_of_nonneg_left (hbd.trans (by linarith)) (by positivity)

/-- Elementary `L^2` difference inequality for interval integrals of `ℂ`-valued functions:
`|∫ a..b ‖f‖^2 - ∫ a..b ‖g‖^2| ≤ (∫ a..b ‖f - g‖^2) + 2 * √(∫ a..b ‖g‖^2) * √(∫ a..b ‖f - g‖^2)`. -/
lemma abs_integral_norm_sq_sub_le {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    |(∫ t in a..b, ‖f t‖ ^ 2) - (∫ t in a..b, ‖g t‖ ^ 2)| ≤
      (∫ t in a..b, ‖f t - g t‖ ^ 2) +
      2 * Real.sqrt (∫ t in a..b, ‖g t‖ ^ 2) * Real.sqrt (∫ t in a..b, ‖f t - g t‖ ^ 2) := by
  have hint_f : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b :=
    (hf.norm.pow 2).intervalIntegrable_of_Icc hab
  have hint_g : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume a b :=
    (hg.norm.pow 2).intervalIntegrable_of_Icc hab
  have hint_fg : IntervalIntegrable (fun t => ‖f t - g t‖ ^ 2) volume a b :=
    ((hf.sub hg).norm.pow 2).intervalIntegrable_of_Icc hab
  have hint_prod : IntervalIntegrable (fun t => ‖g t‖ * ‖f t - g t‖) volume a b :=
    (hg.norm.mul (hf.sub hg).norm).intervalIntegrable_of_Icc hab
  -- Pointwise: `|‖f t‖^2 - ‖g t‖^2| ≤ ‖f t - g t‖^2 + 2 * ‖g t‖ * ‖f t - g t‖`
  have hpt : ∀ t ∈ Set.Icc a b,
      |‖f t‖ ^ 2 - ‖g t‖ ^ 2| ≤ ‖f t - g t‖ ^ 2 + 2 * (‖g t‖ * ‖f t - g t‖) := by
    intro t _
    have hdiff : |‖f t‖ - ‖g t‖| ≤ ‖f t - g t‖ := abs_norm_sub_norm_le (f t) (g t)
    have hsum : ‖f t‖ + ‖g t‖ ≤ 2 * ‖g t‖ + ‖f t - g t‖ := by
      have : ‖f t‖ - ‖g t‖ ≤ ‖f t - g t‖ := (abs_le.mp hdiff).2
      linarith
    calc |‖f t‖ ^ 2 - ‖g t‖ ^ 2|
        = |‖f t‖ - ‖g t‖| * (‖f t‖ + ‖g t‖) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          ring
      _ ≤ ‖f t - g t‖ * (2 * ‖g t‖ + ‖f t - g t‖) :=
          mul_le_mul hdiff hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖f t - g t‖ ^ 2 + 2 * (‖g t‖ * ‖f t - g t‖) := by ring
  -- Cauchy–Schwarz on `∫ ‖g‖ * ‖f - g‖ ≤ √(∫ ‖g‖^2) * √(∫ ‖f - g‖^2)`
  have hcs : ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ ≤
      Real.sqrt (∫ t in a..b, ‖g t‖ ^ 2) * Real.sqrt (∫ t in a..b, ‖f t - g t‖ ^ 2) := by
    set A := ∫ t in a..b, ‖g t‖ ^ 2
    set B := ∫ t in a..b, ‖f t - g t‖ ^ 2
    have hA : 0 ≤ A := intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
    have hB : 0 ≤ B := intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
    by_cases hAB : A = 0 ∨ B = 0
    · -- If `A = 0` or `B = 0`, for every `ε > 0`, `2 * ∫ ‖g‖*‖f-g‖ ≤ ε * A + ε⁻¹ * B`!
      have h0 : ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ ≤ 0 := by
        rcases hAB with hA0 | hB0
        · by_contra hpos; push Not at hpos
          set ε : ℝ := (B + 1) / (∫ t in a..b, ‖g t‖ * ‖f t - g t‖)
          have hε : 0 < ε := by positivity
          have h1 : 2 * ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ ≤ ε * A + ε⁻¹ * B := by
            have hpt' : ∀ t ∈ Set.Icc a b, 2 * (‖g t‖ * ‖f t - g t‖) ≤ ε * ‖g t‖ ^ 2 + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
              intro t _
              have hsq := sq_nonneg (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε)
              have hne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
              have hexp : (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε) ^ 2 =
                  ε * ‖g t‖ ^ 2 - 2 * (‖g t‖ * ‖f t - g t‖) + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
                field_simp [hne]; rw [Real.sq_sqrt hε.le]; field_simp [hε.ne']; ring
              linarith
            have hm := intervalIntegral.integral_mono_on hab (hint_prod.const_mul 2)
              ((hint_g.const_mul ε).add (hint_fg.const_mul ε⁻¹)) hpt'
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
              (hint_g.const_mul ε) (hint_fg.const_mul ε⁻¹),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
            exact hm
          rw [hA0, mul_zero, zero_add] at h1
          have hinv : ε⁻¹ * B = (B / (B + 1)) * ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ := by
            dsimp only [ε]; field_simp [(by linarith : B + 1 ≠ 0), hpos.ne']
          rw [hinv] at h1
          have hlt1 : B / (B + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          nlinarith
        · by_contra hpos; push Not at hpos
          set ε : ℝ := (∫ t in a..b, ‖g t‖ * ‖f t - g t‖) / (A + 1)
          have hε : 0 < ε := by positivity
          have h1 : 2 * ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ ≤ ε * A + ε⁻¹ * B := by
            have hpt' : ∀ t ∈ Set.Icc a b, 2 * (‖g t‖ * ‖f t - g t‖) ≤ ε * ‖g t‖ ^ 2 + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
              intro t _
              have hsq := sq_nonneg (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε)
              have hne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
              have hexp : (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε) ^ 2 =
                  ε * ‖g t‖ ^ 2 - 2 * (‖g t‖ * ‖f t - g t‖) + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
                field_simp [hne]; rw [Real.sq_sqrt hε.le]; field_simp [hε.ne']; ring
              linarith
            have hm := intervalIntegral.integral_mono_on hab (hint_prod.const_mul 2)
              ((hint_g.const_mul ε).add (hint_fg.const_mul ε⁻¹)) hpt'
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
              (hint_g.const_mul ε) (hint_fg.const_mul ε⁻¹),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
            exact hm
          rw [hB0, mul_zero, add_zero] at h1
          have hmul : ε * A = (A / (A + 1)) * ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ := by
            dsimp only [ε]; field_simp [(by linarith : A + 1 ≠ 0)]
          rw [hmul] at h1
          have hlt1 : A / (A + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          nlinarith
      exact h0.trans (by positivity)
    · push Not at hAB
      have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAB.1)
      have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hAB.2)
      set ε : ℝ := Real.sqrt B / Real.sqrt A
      have hε : 0 < ε := by positivity
      have hpt' : ∀ t ∈ Set.Icc a b, 2 * (‖g t‖ * ‖f t - g t‖) ≤ ε * ‖g t‖ ^ 2 + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
        intro t _
        have hsq := sq_nonneg (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε)
        have hne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
        have hexp : (Real.sqrt ε * ‖g t‖ - ‖f t - g t‖ / Real.sqrt ε) ^ 2 =
            ε * ‖g t‖ ^ 2 - 2 * (‖g t‖ * ‖f t - g t‖) + ε⁻¹ * ‖f t - g t‖ ^ 2 := by
          field_simp [hne]; rw [Real.sq_sqrt hε.le]; field_simp [hε.ne']; ring
        linarith
      have hm := intervalIntegral.integral_mono_on hab (hint_prod.const_mul 2)
        ((hint_g.const_mul ε).add (hint_fg.const_mul ε⁻¹)) hpt'
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hint_g.const_mul ε) (hint_fg.const_mul ε⁻¹),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
      have hRHS_eq : ε * A + ε⁻¹ * B = 2 * (Real.sqrt A * Real.sqrt B) := by
        dsimp only [ε]
        have h1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
          field_simp [(Real.sqrt_pos.mpr hApos).ne']
          nlinarith [Real.mul_self_sqrt hA]
        have h2 : (Real.sqrt B / Real.sqrt A)⁻¹ * B = Real.sqrt A * Real.sqrt B := by
          rw [inv_div]
          field_simp [(Real.sqrt_pos.mpr hBpos).ne']
          nlinarith [Real.mul_self_sqrt hB]
        linarith
      linarith
  rw [← intervalIntegral.integral_sub hint_f hint_g]
  calc |∫ t in a..b, (‖f t‖ ^ 2 - ‖g t‖ ^ 2)|
      ≤ ∫ t in a..b, |‖f t‖ ^ 2 - ‖g t‖ ^ 2| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, (‖f t - g t‖ ^ 2 + 2 * (‖g t‖ * ‖f t - g t‖)) :=
        intervalIntegral.integral_mono_on hab (((hf.norm.pow 2).sub (hg.norm.pow 2)).abs.intervalIntegrable_of_Icc hab)
          (hint_fg.add (hint_prod.const_mul 2)) hpt
    _ = (∫ t in a..b, ‖f t - g t‖ ^ 2) + 2 * ∫ t in a..b, ‖g t‖ * ‖f t - g t‖ := by
        rw [intervalIntegral.integral_add hint_fg (hint_prod.const_mul 2), intervalIntegral.integral_const_mul]
    _ ≤ (∫ t in a..b, ‖f t - g t‖ ^ 2) +
        2 * Real.sqrt (∫ t in a..b, ‖g t‖ ^ 2) * Real.sqrt (∫ t in a..b, ‖f t - g t‖ ^ 2) := by
        linarith

/-- **Unconditional Second Moment of `riemannZeta` on `[1, T]` for EVERY `σ > 1/2`** (including `σ = 1`!):
`Filter.Tendsto (fun T : ℝ => (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ^ 2) Filter.atTop (nhds ((riemannZeta (2 * (σ : ℂ))).re))`. -/
theorem riemannZeta_second_moment_Icc_tendsto {σ : ℝ} (hσ : 1 / 2 < σ) :
    Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2)
      Filter.atTop (nhds ((riemannZeta (2 * (σ : ℂ))).re)) := by
  have hσ0 : 0 < σ := by linarith
  set L : ℝ := (riemannZeta (2 * (σ : ℂ))).re
  let a : ℕ → ℂ := fun n => (n : ℂ) ^ (-(σ : ℂ))
  let D : ℕ → ℝ → ℂ := fun N t => dirichletPoly a N (Complex.I * (t : ℂ))
  -- Symmetry `‖D N (-t)‖ = ‖D N t‖`, so `∫_0^T ‖D N t‖^2 = (1/2) * ∫_{-T}^T ‖D N t‖^2`
  have hD_even : ∀ N : ℕ, ∀ t : ℝ, ‖D N (-t)‖ = ‖D N t‖ := by
    intro N t
    have hconj : star (D N t) = D N (-t) := by
      dsimp only [D, dirichletPoly, a]
      rw [star_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [star_mul', nat_cpow_neg_I_mul n hn1 t, nat_cpow_neg_I_mul n hn1 (-t)]
      have h1 : star ((n : ℂ) ^ (-(σ : ℂ))) = (n : ℂ) ^ (-(σ : ℂ)) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le,
          Complex.star_def, Complex.conj_ofReal]
      have h2 : star (Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) =
          Complex.exp (-Complex.I * ((-t : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        rw [Complex.star_def, ← Complex.exp_conj]
        simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
        congr 1; push_cast; ring
      rw [h1, h2, mul_comm]
    rw [← hconj, norm_star]
  have hD_cont : ∀ N : ℕ, Continuous (D N) := by
    intro N
    dsimp only [D, dirichletPoly]
    refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
    have hfn : (fun t : ℝ => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
        fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) :=
      funext fun t => nat_cpow_neg_I_mul n (Finset.mem_Icc.mp hn).1 t
    rw [hfn]
    exact Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have hD_half : ∀ N : ℕ, ∀ T : ℝ,
      ∫ t in (0 : ℝ)..T, ‖D N t‖ ^ 2 = (1 / 2) * ∫ t in (-T : ℝ)..T, ‖D N t‖ ^ 2 := by
    intro N T
    have hc : Continuous (fun t : ℝ => ‖D N t‖ ^ 2) := (hD_cont N).norm.pow 2
    have hneg : ∫ t in (-T : ℝ)..(0 : ℝ), ‖D N t‖ ^ 2 = ∫ t in (0 : ℝ)..T, ‖D N t‖ ^ 2 := by
      have hcomp := intervalIntegral.integral_comp_neg (f := fun t => ‖D N t‖ ^ 2) (a := (0 : ℝ)) (b := T)
      simp only [neg_zero] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hD_even N t]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (-T) 0) (hc.intervalIntegrable 0 T)
    linarith
  have hceil_top : Tendsto (fun T : ℝ => ⌈T⌉₊) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun n => ⟨(n : ℝ), fun T hT => Nat.cast_le.mp (hT.trans (Nat.le_ceil T))⟩
  -- Step 1: `(1 / T) * ∫_0^T ‖D ⌈T⌉₊ t‖^2 dt → L`
  have hD_main : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) atTop (nhds L) := by
    have hsum_tend : Tendsto (fun T : ℝ => ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)) atTop (nhds L) :=
      (tendsto_sum_rpow_neg_two_mul hσ).comp hceil_top
    have herr_tend : Tendsto (fun T : ℝ =>
        (8 * Real.pi + 10) / 2 * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)))
        atTop (nhds 0) := by
      simpa using (sum_rpow_one_sub_two_mul_div_tendsto_zero hσ).const_mul ((8 * Real.pi + 10) / 2)
    rw [Metric.tendsto_atTop] at hsum_tend herr_tend ⊢
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := hsum_tend (ε / 2) (by linarith)
    obtain ⟨T₂, hT₂⟩ := herr_tend (ε / 2) (by linarith)
    refine ⟨max 1 (max T₁ T₂), fun T hT => ?_⟩
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hT)
    have h1 := hT₁ T ((le_max_left _ _).trans ((le_max_right _ _).trans hT))
    have h2 := hT₂ T ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
    rw [Real.dist_eq] at h1 h2 ⊢
    rw [sub_zero] at h2
    have hmv := dirichletPoly_mean_value_exact_bound ⌈T⌉₊ T a
    have hnorm_a : ∀ n ∈ Finset.Icc 1 ⌈T⌉₊, ‖a n‖ ^ 2 = (n : ℝ) ^ (-2 * σ) := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
      dsimp only [a]
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
        show (-(σ : ℂ)).re = -σ by simp, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1; ring
    have hnorm_na : ∀ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) * ‖a n‖ ^ 2 = (n : ℝ) ^ (1 - 2 * σ) := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
      rw [hnorm_a n hn,
        show (n : ℝ) * (n : ℝ) ^ (-2 * σ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * σ) by rw [Real.rpow_one],
        ← Real.rpow_add hn0]
      congr 1; ring
    rw [Finset.sum_congr rfl hnorm_a, Finset.sum_congr rfl hnorm_na] at hmv
    have hdiff : (1 / T) * (∫ t in (0 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) - ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ) =
        (1 / (2 * T)) * ((∫ t in (-T : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) - 2 * T * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)) := by
      rw [hD_half]; field_simp [hTpos.ne']
    have hbd1 : |(1 / T) * (∫ t in (0 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) - ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)| ≤
        (8 * Real.pi + 10) / 2 * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)) := by
      rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
      have hle := mul_le_mul_of_nonneg_left hmv (by positivity : 0 ≤ 1 / (2 * T))
      linarith [show 1 / (2 * T) * ((8 * Real.pi + 10) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)) =
        (8 * Real.pi + 10) / 2 * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)) by ring]
    have hnn : 0 ≤ (8 * Real.pi + 10) / 2 * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)) :=
      mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    rw [abs_of_nonneg hnn] at h2
    calc |(1 / T) * (∫ t in (0 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) - L|
        ≤ |(1 / T) * (∫ t in (0 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) - ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)| +
          |∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ) - L| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt hbd1 h2) h1
      _ = ε := by ring
  -- Step 2: `(1 / T) * ∫_0^1 ‖D ⌈T⌉₊ t‖^2 dt → 0`
  have hD_01 : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..(1 : ℝ), ‖D ⌈T⌉₊ t‖ ^ 2) atTop (nhds 0) := by
    -- By `dirichletPoly_mean_value_upper` on `[-1, 1]`, `∫_0^1 ‖D N t‖^2 ≤ (1/2) * (2 + C * N) * ...` — wait:
    -- even simpler, `‖D N t‖^2 ≤ (∑_{n=1}^N n^(-σ))^2`! Wait: for `σ > 1/2`, `(∑_{n=1}^N n^(-σ))^2 = O(N^(2-2σ)) = o(T)`!
    -- Even better: `dirichletPoly_mean_value_exact_bound N 1 a` ALREADY gives:
    -- `∫_0^1 ‖D N t‖^2 ≤ ∑ n^(-2σ) + ((8π + 10) / 2) * ∑ n^(1 - 2σ)`!!
    have hupper : Tendsto (fun T : ℝ =>
        (1 / T) * (∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)) +
        ((8 * Real.pi + 10) / 2) * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun T : ℝ => (1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)) atTop (nhds 0) := by
        have hinv : Tendsto (fun T : ℝ => 1 / T) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
        simpa using hinv.mul ((tendsto_sum_rpow_neg_two_mul hσ).comp hceil_top)
      have h2 : Tendsto (fun T : ℝ =>
          ((8 * Real.pi + 10) / 2) * ((1 / T) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ)))
          atTop (nhds 0) := by
        simpa using (sum_rpow_one_sub_two_mul_div_tendsto_zero hσ).const_mul ((8 * Real.pi + 10) / 2)
      simpa using h1.add h2
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hmv := (abs_le.mp (dirichletPoly_mean_value_exact_bound ⌈T⌉₊ 1 a)).2
      have hnorm_a : ∀ n ∈ Finset.Icc 1 ⌈T⌉₊, ‖a n‖ ^ 2 = (n : ℝ) ^ (-2 * σ) := by
        intro n hn
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
        dsimp only [a]
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
          show (-(σ : ℂ)).re = -σ by simp, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1; ring
      have hnorm_na : ∀ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) * ‖a n‖ ^ 2 = (n : ℝ) ^ (1 - 2 * σ) := by
        intro n hn
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
        rw [hnorm_a n hn,
          show (n : ℝ) * (n : ℝ) ^ (-2 * σ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * σ) by rw [Real.rpow_one],
          ← Real.rpow_add hn0]
        congr 1; ring
      rw [Finset.sum_congr rfl hnorm_a, Finset.sum_congr rfl hnorm_na] at hmv
      have h01_le : ∫ t in (0 : ℝ)..(1 : ℝ), ‖D ⌈T⌉₊ t‖ ^ 2 ≤
          (∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (-2 * σ)) +
          ((8 * Real.pi + 10) / 2) * ∑ n ∈ Finset.Icc 1 ⌈T⌉₊, (n : ℝ) ^ (1 - 2 * σ) := by
        rw [hD_half ⌈T⌉₊ 1]; linarith
      have hmul := mul_le_mul_of_nonneg_left h01_le (by positivity : 0 ≤ 1 / T)
      linarith
  -- Hence `(1 / T) * ∫_1^T ‖D ⌈T⌉₊ t‖^2 dt → L`
  have hD_1T : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) atTop (nhds L) := by
    have hsub := hD_main.sub hD_01
    rw [sub_zero] at hsub
    refine hsub.congr fun T => ?_
    have hc : Continuous (fun t : ℝ => ‖D ⌈T⌉₊ t‖ ^ 2) := (hD_cont ⌈T⌉₊).norm.pow 2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 T)
    rw [← hadd]; ring
  -- Step 3: `L^2` error `(1 / T) * ∫_1^T ‖ζ(σ + I*t) - D ⌈T⌉₊ t‖^2 dt → 0`
  have hE_tend : Tendsto (fun T : ℝ =>
      (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2)
      atTop (nhds 0) := by
    set γ : ℝ := max 0 (2 - 2 * σ)
    have hγ0 : 0 ≤ γ := le_max_left _ _
    have hγ1 : γ < 1 := max_lt zero_lt_one (by linarith)
    have hupper : Tendsto (fun T : ℝ =>
        2 * (T + 1) ^ γ / T + 8 * T ^ (-2 * σ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun T : ℝ => 2 * ((1 + 1 / T) ^ γ * T ^ (γ - 1))) atTop (nhds 0) := by
        have hinv : Tendsto (fun T : ℝ => 1 / T) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
        have ha : Tendsto (fun T : ℝ => (1 + 1 / T) ^ γ) atTop (nhds ((1 + 0) ^ γ)) :=
          (tendsto_const_nhds.add hinv).rpow_const (Or.inl (by norm_num))
        have hb : Tendsto (fun T : ℝ => T ^ (γ - 1)) atTop (nhds 0) :=
          (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - γ)).congr fun T => by congr 1; ring
        simpa using (ha.mul hb).const_mul 2
      have h2 : Tendsto (fun T : ℝ => 8 * T ^ (-2 * σ)) atTop (nhds 0) := by
        simpa [neg_mul] using (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * σ)).const_mul 8
      have hsum := h1.add h2
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hTp1 : T + 1 = T * (1 + 1 / T) := by field_simp [hT.ne']
      rw [hTp1, Real.mul_rpow hT.le (by positivity)]
      have hdivT : T ^ γ / T = T ^ (γ - 1) := by
        rw [show T ^ γ / T = T ^ γ / T ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_sub hT]
      rw [show 2 * (T ^ γ * (1 + 1 / T) ^ γ) / T =
        2 * ((1 + 1 / T) ^ γ * (T ^ γ / T)) by ring, hdivT]
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _)
    · filter_upwards [eventually_ge_atTop (max 2 (σ + 1))] with T hT
      have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
      have hTσ : σ + 1 ≤ T := (le_max_right _ _).trans hT
      have hT1 : 1 ≤ T := by linarith
      set N : ℕ := ⌈T⌉₊
      have hTN : T ≤ (N : ℝ) := Nat.le_ceil T
      have hNT1 : (N : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      have hN1 : 1 ≤ N := by
        have : (1 : ℝ) ≤ (N : ℝ) := by linarith
        exact Nat.one_le_cast.mp this
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      -- Continuity of `ζ(σ + I*t)` on `[1, T]`
      have hlin : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) :=
        continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      have hzeta_cont : ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) (Set.Icc 1 T) := by
        intro t ht
        have hs1 : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
          intro h; have him := congrArg Complex.im h; simp at him; linarith [ht.1]
        have hd : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) :=
          differentiableAt_riemannZeta hs1
        exact (ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (σ : ℂ) + Complex.I * (u : ℂ))
          hd.continuousAt hlin.continuousAt).continuousWithinAt
      have hpt_E : ∀ t ∈ Set.Icc (1 : ℝ) T,
          ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D N t‖ ^ 2 ≤
          2 * (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 + 8 * (N : ℝ) ^ (-2 * σ) := by
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hs1 : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
          intro h; have him := congrArg Complex.im h; simp at him; linarith [ht.1]
        have hap := riemannZeta_approx_eulerMaclaurin hN1 hσ0 hs1
          (by rw [abs_of_pos ht0]; linarith [ht.2]) (by linarith)
        have hpole : ‖(N : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) /
            (((σ : ℂ) + Complex.I * (t : ℂ)) - 1)‖ ≤ (N : ℝ) ^ (1 - σ) / t := by
          rw [norm_div, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0,
            show (1 - ((σ : ℂ) + Complex.I * (t : ℂ))).re = 1 - σ by simp]
          have hden : t ≤ ‖((σ : ℂ) + Complex.I * (t : ℂ)) - 1‖ := by
            calc t = |(((σ : ℂ) + Complex.I * (t : ℂ)) - 1).im| := by simp [abs_of_pos ht0]
              _ ≤ ‖((σ : ℂ) + Complex.I * (t : ℂ)) - 1‖ := Complex.abs_im_le_norm _
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) ht0 hden
        have htri : ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D N t‖ ≤
            (N : ℝ) ^ (1 - σ) / t + 2 * (N : ℝ) ^ (-σ) := by
          have h1 := norm_add_le
            (riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D N t -
              (N : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) / (((σ : ℂ) + Complex.I * (t : ℂ)) - 1))
            ((N : ℂ) ^ (1 - ((σ : ℂ) + Complex.I * (t : ℂ))) / (((σ : ℂ) + Complex.I * (t : ℂ)) - 1))
          rw [sub_add_cancel] at h1
          linarith
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        have hamgm : ((N : ℝ) ^ (1 - σ) / t + 2 * (N : ℝ) ^ (-σ)) ^ 2 ≤
            2 * ((N : ℝ) ^ (1 - σ) / t) ^ 2 + 2 * (2 * (N : ℝ) ^ (-σ)) ^ 2 := by
          nlinarith [sq_nonneg ((N : ℝ) ^ (1 - σ) / t - 2 * (N : ℝ) ^ (-σ))]
        have hpow1 : ((N : ℝ) ^ (1 - σ) / t) ^ 2 = (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 := by
          rw [div_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 - σ)) 2, ← Real.rpow_mul hN0.le]
          congr 2; ring
        have hpow2 : ((N : ℝ) ^ (-σ)) ^ 2 = (N : ℝ) ^ (-2 * σ) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hN0.le]
          congr 1; ring
        calc ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D N t‖ ^ 2
            ≤ 2 * ((N : ℝ) ^ (1 - σ) / t) ^ 2 + 2 * (2 * (N : ℝ) ^ (-σ)) ^ 2 := hsq.trans hamgm
          _ = 2 * (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 + 8 * (N : ℝ) ^ (-2 * σ) := by
              rw [hpow1, mul_pow, hpow2]; ring
      have hint_rhs : IntervalIntegrable
          (fun t : ℝ => 2 * (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 + 8 * (N : ℝ) ^ (-2 * σ)) volume 1 T :=
        ((continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
          rw [Set.uIcc_of_le hT1] at ht; exact pow_ne_zero 2 (by dsimp only [id]; linarith [ht.1])).add
          continuousOn_const).intervalIntegrable
      have hmono := intervalIntegral.integral_mono_on hT1
        (((hzeta_cont.sub (hD_cont N).continuousOn).norm.pow 2).intervalIntegrable_of_Icc hT1)
        hint_rhs hpt_E
      have hinv2 : ∫ t in (1 : ℝ)..T, (1 : ℝ) / t ^ 2 = 1 - 1 / T := by
        have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / t ^ 2) t := by
          intro t ht
          rw [Set.uIcc_of_le hT1] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have h := (hasDerivAt_inv ht0).neg
          refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [one_div])).congr_deriv ?_
          field_simp [ht0]
        have hc : ContinuousOn (fun u : ℝ => (1 : ℝ) / u ^ 2) (Set.uIcc (1 : ℝ) T) :=
          continuousOn_const.div (continuousOn_id.pow 2) fun u hu => by
            rw [Set.uIcc_of_le hT1] at hu; exact pow_ne_zero 2 (by linarith [hu.1])
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
        ring
      have hrhs_val : ∫ t in (1 : ℝ)..T, (2 * (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 + 8 * (N : ℝ) ^ (-2 * σ)) ≤
          2 * (N : ℝ) ^ (2 - 2 * σ) + 8 * T * (N : ℝ) ^ (-2 * σ) := by
        have hrew : (fun t : ℝ => 2 * (N : ℝ) ^ (2 - 2 * σ) / t ^ 2 + 8 * (N : ℝ) ^ (-2 * σ)) =
            fun t : ℝ => (2 * (N : ℝ) ^ (2 - 2 * σ)) * (1 / t ^ 2) + 8 * (N : ℝ) ^ (-2 * σ) := by
          funext t; ring
        have hc1 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t ^ 2) volume 1 T :=
          (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
            rw [Set.uIcc_of_le hT1] at ht; exact pow_ne_zero 2 (by dsimp only [id]; linarith [ht.1])).intervalIntegrable
        rw [hrew, intervalIntegral.integral_add (hc1.const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, hinv2, intervalIntegral.integral_const, smul_eq_mul]
        have h1 : 1 - 1 / T ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / T by positivity]
        have h2 : T - 1 ≤ T := by linarith
        nlinarith [Real.rpow_nonneg hN0.le (2 - 2 * σ), Real.rpow_nonneg hN0.le (-2 * σ)]
      have hN_pow1 : (N : ℝ) ^ (2 - 2 * σ) ≤ (T + 1) ^ γ := by
        have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
        calc (N : ℝ) ^ (2 - 2 * σ)
            ≤ (N : ℝ) ^ γ := Real.rpow_le_rpow_of_exponent_le hN_ge1 (le_max_right _ _)
          _ ≤ (T + 1) ^ γ := Real.rpow_le_rpow hN0.le hNT1 hγ0
      have hN_pow2 : (N : ℝ) ^ (-2 * σ) ≤ T ^ (-2 * σ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hTN (by linarith)
      have hmul := mul_le_mul_of_nonneg_left (hmono.trans hrhs_val) (by positivity : 0 ≤ 1 / T)
      have halg : (1 / T) * (2 * (N : ℝ) ^ (2 - 2 * σ) + 8 * T * (N : ℝ) ^ (-2 * σ)) =
          2 * (N : ℝ) ^ (2 - 2 * σ) / T + 8 * (N : ℝ) ^ (-2 * σ) := by
        field_simp [(by linarith : T ≠ 0)]
      rw [halg] at hmul
      calc (1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D N t‖ ^ 2
          ≤ 2 * (N : ℝ) ^ (2 - 2 * σ) / T + 8 * (N : ℝ) ^ (-2 * σ) := hmul
        _ ≤ 2 * (T + 1) ^ γ / T + 8 * T ^ (-2 * σ) := by gcongr
  -- Step 4: Combine `hD_1T` and `hE_tend` via `abs_integral_norm_sq_sub_le`!
  have hdiff_tend : Tendsto (fun T : ℝ =>
      ((1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) -
      ((1 / T) * ∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2)) atTop (nhds 0) := by
    have hupper : Tendsto (fun T : ℝ =>
        ((1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2) +
        2 * Real.sqrt ((1 / T) * ∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) *
          Real.sqrt ((1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2))
        atTop (nhds 0) := by
      have h1 := hE_tend
      have h2 := ((hD_1T.sqrt.const_mul 2).mul hE_tend.sqrt)
      simpa using h1.add h2
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTpos : 0 < T := by linarith
    have hlin : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) :=
      continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
    have hzeta_cont : ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) (Set.Icc 1 T) := by
      intro t ht
      have hs1 : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
        intro h; have him := congrArg Complex.im h; simp at him; linarith [ht.1]
      exact (ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (σ : ℂ) + Complex.I * (u : ℂ))
        (differentiableAt_riemannZeta hs1).continuousAt hlin.continuousAt).continuousWithinAt
    have habs := abs_integral_norm_sq_sub_le hT hzeta_cont (hD_cont ⌈T⌉₊).continuousOn
    have hsub_eq : (1 / T) * (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) -
        (1 / T) * (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) =
        (1 / T) * ((∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) -
          (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2)) := by ring
    rw [Real.norm_eq_abs, hsub_eq, abs_mul, abs_of_pos (by positivity : 0 < 1 / T)]
    have hmul := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 1 / T)
    have hsqrt_pull : (1 / T) * (2 * Real.sqrt (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) *
          Real.sqrt (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2)) =
        2 * Real.sqrt ((1 / T) * ∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) *
          Real.sqrt ((1 / T) * ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 1 / T), Real.sqrt_mul (by positivity : 0 ≤ 1 / T)]
      have hsq : Real.sqrt (1 / T) * Real.sqrt (1 / T) = 1 / T := Real.mul_self_sqrt (by positivity)
      calc (1 / T) * (2 * Real.sqrt (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) *
              Real.sqrt (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2))
          = 2 * (Real.sqrt (1 / T) * Real.sqrt (1 / T)) * Real.sqrt (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2) *
              Real.sqrt (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2) := by
            rw [hsq]; ring
        _ = 2 * (Real.sqrt (1 / T) * Real.sqrt (∫ t in (1 : ℝ)..T, ‖D ⌈T⌉₊ t‖ ^ 2)) *
              (Real.sqrt (1 / T) * Real.sqrt (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) - D ⌈T⌉₊ t‖ ^ 2)) := by
            ring
    linarith
  have hfinal := hdiff_tend.add hD_1T
  rw [zero_add] at hfinal
  exact hfinal.congr fun T => by ring

/-- **Unconditional Second Moment of `riemannZeta` on `[-T, T]` for EVERY `σ > 1/2`, `σ ≠ 1`**:
`Filter.Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ^ 2) Filter.atTop (nhds ((riemannZeta (2 * (σ : ℂ))).re))`.
(Note: at `σ = 1`, `‖ζ(1 + it)‖² ~ 1/t²` is not integrable at `t = 0`, where
`riemannZeta_second_moment_Icc_tendsto` gives the exact `[1, T]` second moment.) -/
theorem riemannZeta_second_moment_tendsto {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≠ 1) :
    Filter.Tendsto
      (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2)
      Filter.atTop (nhds ((riemannZeta (2 * (σ : ℂ))).re)) := by
  have hσ0 : 0 < σ := by linarith
  -- Continuity of `t ↦ riemannZeta (σ + I * t)` on ALL of `ℝ` (since `σ ≠ 1`)
  have hlin : Continuous (fun t : ℝ => (σ : ℂ) + Complex.I * (t : ℂ)) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hzeta_cont : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs1 : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; exact hσ1 hre
    exact ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (σ : ℂ) + Complex.I * (u : ℂ))
      (differentiableAt_riemannZeta hs1).continuousAt hlin.continuousAt
  -- Evenness `‖riemannZeta (σ - I * t)‖ = ‖riemannZeta (σ + I * t)‖` from `riemannZeta_eq_eulerMaclaurin_trunc`!
  have hzeta_even : ∀ t : ℝ, ‖riemannZeta ((σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ))‖ =
      ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    intro t
    have hs_ne : (σ : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; exact hσ1 hre
    have hs_ne' : (σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) ≠ 1 := by
      intro h; have hre := congrArg Complex.re h; simp at hre; exact hσ1 hre
    have hconj_s : starRingEnd ℂ ((σ : ℂ) + Complex.I * (t : ℂ)) = (σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ) := by
      simp [Complex.conj_ofReal, Complex.conj_I]
    -- Apply `riemannZeta_sub_pole_eq_eulerMaclaurin` and conjugate both sides!
    have h1 := Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin (s := (σ : ℂ) + Complex.I * (t : ℂ))
      (by simp [hσ0]) hs_ne
    have h2 := Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin (s := (σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ))
      (by simp [hσ0]) hs_ne'
    have h1c := congrArg (starRingEnd ℂ) h1
    simp only [map_sub, map_div₀, map_one, map_mul, hconj_s] at h1c
    have hint_conj : (starRingEnd ℂ) (∫ u in Ioi (1 : ℝ),
          ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 1)) =
        ∫ u in Ioi (1 : ℝ), ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) *
          (u : ℂ) ^ (-((σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) - 1) := by
      change Complex.conjCLE (∫ u in Ioi (1 : ℝ),
          ((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 1)) = _
      rw [← Complex.conjCLE.integral_comp_comm]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := zero_lt_one.trans hu
      change (starRingEnd ℂ) (((Stage5ZetaZeroFree.fractNat u : ℝ) : ℂ) *
        (u : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)) - 1)) = _
      rw [map_mul, Complex.conj_ofReal, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'),
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu0.ne'), ← Complex.ofReal_log hu0.le,
        ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_ofReal, map_sub, map_neg, map_one, hconj_s]
    rw [hint_conj] at h1c
    have heq : riemannZeta ((σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
        starRingEnd ℂ (riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) := by
      linear_combination h2 - h1c
    rw [heq, Complex.norm_conj]
  -- Split `(-T)..T` into `(-T)..(-1) + (-1)..1 + 1..T`!
  have h1T := riemannZeta_second_moment_Icc_tendsto hσ
  have hmid : Tendsto (fun T : ℝ =>
      (1 / (2 * T)) * ∫ t in (-1 : ℝ)..(1 : ℝ), ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2)
      atTop (nhds 0) := by
    have hinv : Tendsto (fun T : ℝ => 1 / (2 * T)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
    simpa using hinv.mul_const _
  have hcomb := h1T.add hmid
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hc : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) :=
    hzeta_cont.norm.pow 2
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-T) (-1)) (hc.intervalIntegrable (-1) 1)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-T) 1) (hc.intervalIntegrable 1 T)
  have hsym : ∫ t in (-T : ℝ)..(-1 : ℝ), ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
      ∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun t => ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) (a := (1 : ℝ)) (b := T)
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hzeta_even t]
  have htot : ∫ t in (-T : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
      2 * (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) +
      ∫ t in (-1 : ℝ)..(1 : ℝ), ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 := by
    linarith
  rw [htot]; field_simp [(by linarith : T ≠ 0)]

/-! ## Section 4: Unconditional Large-Sieve Zero-Detecting Bound (Montgomery–Halász Engine) -/

/-- The Dirichlet mollifier `M_X(s) = ∑_{n=1}^X μ(n) n^(-s)`. -/
def mollifierPoly (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)

/-- Mollified convolution coefficients `c_n(X) = ∑_{d ∣ n, d ≤ X} μ(d)` arising in
`ζ(s) M_X(s) - 1 = ∑_{n > X} c_n(X) n^(-s)`. -/
def mollifiedCoeff (X n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (· ≤ X), (ArithmeticFunction.moebius d : ℂ)

lemma mollifiedCoeff_one {X : ℕ} (hX : 1 ≤ X) : mollifiedCoeff X 1 = 1 := by
  dsimp only [mollifiedCoeff]
  have hfilt : (1 : ℕ).divisors.filter (· ≤ X) = {1} := by
    ext d; simp only [Nat.divisors_one, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hX⟩⟩
  rw [hfilt, Finset.sum_singleton]
  simp

lemma mollifiedCoeff_eq_zero_of_le {X n : ℕ} (hn2 : 2 ≤ n) (hnX : n ≤ X) :
    mollifiedCoeff X n = 0 := by
  dsimp only [mollifiedCoeff]
  have hfilt : n.divisors.filter (· ≤ X) = n.divisors := by
    refine Finset.filter_true_of_mem fun d hd => ?_
    exact (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hnX
  rw [hfilt]
  have hZ : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
    have hmul := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) n
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg (by omega)] at hmul
    rw [← hmul]
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hq : n / d ≠ 0 := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hdle := Nat.le_of_dvd (by omega) hdvd
      exact Nat.div_ne_zero_iff.mpr ⟨(Nat.pos_of_mem_divisors hd).ne', hdle⟩
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq]
  exact_mod_cast hZ

lemma norm_mollifiedCoeff_le_divisors (X n : ℕ) :
    ‖mollifiedCoeff X n‖ ≤ (n.divisors.card : ℝ) := by
  dsimp only [mollifiedCoeff]
  calc ‖∑ d ∈ n.divisors.filter (· ≤ X), (ArithmeticFunction.moebius d : ℂ)‖
      ≤ ∑ d ∈ n.divisors.filter (· ≤ X), ‖(ArithmeticFunction.moebius d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ n.divisors.filter (· ≤ X), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        by_cases hsq : Squarefree d
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp [norm_pow]
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
    _ = ((n.divisors.filter (· ≤ X)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)

/-- Submultiplicativity of the divisor count: `d(a * b) ≤ d(a) * d(b)` for `a, b ≥ 1`. -/
lemma divisors_card_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    have hdvd : d ∣ a * b := Nat.dvd_of_mem_divisors hd
    set x := Nat.gcd d a
    have hx_dvd_d : x ∣ d := Nat.gcd_dvd_left d a
    have hx_dvd_a : x ∣ a := Nat.gcd_dvd_right d a
    have hx_pos : 0 < x := Nat.gcd_pos_of_pos_right d (by omega)
    set y := d / x
    have hxy : x * y = d := Nat.mul_div_cancel' hx_dvd_d
    have hy_dvd_b : y ∣ b := by
      have hcop : Nat.Coprime (d / x) (a / x) := Nat.coprime_div_gcd_div_gcd hx_pos
      have hdvd' : (d / x) ∣ (a / x) * b := by
        have h1 : x * (d / x) ∣ x * ((a / x) * b) := by
          rw [Nat.mul_div_cancel' hx_dvd_d, ← mul_assoc, Nat.mul_div_cancel' hx_dvd_a]
          exact hdvd
        exact (mul_dvd_mul_iff_left hx_pos.ne').mp h1
      exact hcop.dvd_of_dvd_mul_left hdvd'
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hx_dvd_a, by omega⟩, Nat.mem_divisors.mpr ⟨hy_dvd_b, by omega⟩⟩, hxy⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by rw [Finset.card_product]))

/-- Elementary harmonic bound: `∑ n ∈ Icc 1 N, 1 / n ≤ 1 + log N` for `1 ≤ N`. -/
lemma sum_inv_le_one_add_log {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction r with
  | zero => simp
  | succ r ih =>
    have hIcc : Finset.Icc 1 (1 + (r + 1)) = insert (1 + (r + 1)) (Finset.Icc 1 (1 + r)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hstep := sub_div_le_log_div (n := 1 + r) (m := 1 + (r + 1)) (by omega) (by omega)
    have hdiff : ((1 + (r + 1) : ℕ) : ℝ) - ((1 + r : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [hdiff, Real.log_div (Nat.cast_pos.mpr (by omega)).ne' (Nat.cast_pos.mpr (by omega)).ne'] at hstep
    linarith [ih (by omega)]

/-- Elementary divisor-squared mean bound:
`∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ N * (1 + Real.log N) ^ 3` for all `N ≥ 1`. -/
lemma sum_divisors_card_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  -- Helper 1: `∑_{b=1}^M d(b) ≤ M * (1 + log M)`
  have hsum_d : ∀ M : ℕ, 1 ≤ M →
      ∑ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
    intro M hM
    have hswap : ∑ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) =
        ∑ c ∈ Finset.Icc 1 M, (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ) := by
      have h1 : ∀ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) =
          ∑ c ∈ Finset.Icc 1 M, if c ∣ b then (1 : ℝ) else 0 := by
        intro b hb
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
        have hbM : b ≤ M := (Finset.mem_Icc.mp hb).2
        have hdiv_eq : b.divisors = (Finset.Icc 1 M).filter (fun c => c ∣ b) := by
          ext c
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨hcb, _⟩
            have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcb (by omega)
            have hcM : c ≤ M := (Nat.le_of_dvd (by omega) hcb).trans hbM
            exact ⟨⟨hc1, hcM⟩, hcb⟩
          · rintro ⟨_, hcb⟩; exact ⟨hcb, by omega⟩
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hdiv_eq]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hswap]
    have hcard : ∀ c ∈ Finset.Icc 1 M,
        (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ) ≤ (M : ℝ) / (c : ℝ) := by
      intro c hc
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      have hsub : (Finset.Icc 1 M).filter (fun b => c ∣ b) ⊆
          (Finset.Icc 1 (M / c)).image (fun k => c * k) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_Icc] at hb
        obtain ⟨k, rfl⟩ := hb.2
        rw [Finset.mem_image]
        refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra hk0; push Not at hk0; have hk : k = 0 := by omega
          subst hk; simp at hb
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [hb.1.2])
      have hle : ((Finset.Icc 1 M).filter (fun b => c ∣ b)).card ≤ M / c :=
        (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
      calc (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ)
          ≤ ((M / c : ℕ) : ℝ) := Nat.cast_le.mpr hle
        _ ≤ (M : ℝ) / (c : ℝ) := by
            rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
            exact_mod_cast Nat.div_mul_le_self M c
    calc ∑ c ∈ Finset.Icc 1 M, (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ)
        ≤ ∑ c ∈ Finset.Icc 1 M, (M : ℝ) / (c : ℝ) := Finset.sum_le_sum hcard
      _ = (M : ℝ) * ∑ c ∈ Finset.Icc 1 M, (1 : ℝ) / (c : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log hM) (Nat.cast_nonneg M)
  -- Helper 2: `∑_{a=1}^N d(a) / a ≤ (1 + log N)^2`
  have hsum_d_div : ∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    have h1 : ∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ) =
        ∑ a ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N, if c ∣ a then (1 : ℝ) / (a : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
      have hdiv_eq : a.divisors = (Finset.Icc 1 N).filter (fun c => c ∣ a) := by
        ext c
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hca, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hca (by omega), (Nat.le_of_dvd (by omega) hca).trans haN⟩, hca⟩
        · rintro ⟨_, hca⟩; exact ⟨hca, by omega⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div, hdiv_eq]
    rw [h1, Finset.sum_comm]
    have hinner : ∀ c ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 N, (if c ∣ a then (1 : ℝ) / (a : ℝ) else 0) ≤
        ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) := by
      intro c hc
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      rw [← Finset.sum_filter]
      have hsub : (Finset.Icc 1 N).filter (fun a => c ∣ a) ⊆
          (Finset.Icc 1 N).image (fun e => c * e) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        obtain ⟨e, rfl⟩ := ha.2
        rw [Finset.mem_image]
        refine ⟨e, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra he0; push Not at he0; have he : e = 0 := (by omega); subst he; simp at ha
        · nlinarith [ha.1.2]
      calc ∑ a ∈ (Finset.Icc 1 N).filter (fun a => c ∣ a), (1 : ℝ) / (a : ℝ)
          ≤ ∑ a ∈ (Finset.Icc 1 N).image (fun e => c * e), (1 : ℝ) / (a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / ((c * e : ℕ) : ℝ) := by
            rw [Finset.sum_image]
            intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
        _ = ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => ?_; push_cast; ring
    calc ∑ c ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, (if c ∣ a then (1 : ℝ) / (a : ℝ) else 0)
        ≤ ∑ c ∈ Finset.Icc 1 N, ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) :=
          Finset.sum_le_sum hinner
      _ = (∑ c ∈ Finset.Icc 1 N, (1 : ℝ) / (c : ℝ)) ^ 2 := by rw [← Finset.sum_mul, sq]
      _ ≤ (1 + Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (sum_inv_le_one_add_log hN) 2
  -- Main step: `∑_{n=1}^N d(n)^2 = ∑_{a=1}^N ∑_{b ≤ N/a} d(a * b) ≤ ∑_{a=1}^N d(a) * ∑_{b ≤ N/a} d(b)`!
  have hdecomp : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 =
        ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, if a ∣ n then (n.divisors.card : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hdiv_eq : n.divisors = (Finset.Icc 1 N).filter (fun a => a ∣ n) := by
        ext a
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨han, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos han (by omega), (Nat.le_of_dvd (by omega) han).trans hnN⟩, han⟩
        · rintro ⟨_, han⟩; exact ⟨han, by omega⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, sq, hdiv_eq]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun n _ => n / a) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨k, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left k (by omega)]
      refine ⟨?_, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [hn.1.2])⟩
      by_contra hk0; push Not at hk0; have hk : k = 0 := (by omega); subst hk; simp at hn
    · intro n₁ hn₁ n₂ hn₂ heq
      have h1' := (Finset.mem_filter.mp hn₁).2
      have h2' := (Finset.mem_filter.mp hn₂).2
      calc n₁ = a * (n₁ / a) := (Nat.mul_div_cancel' h1').symm
        _ = a * (n₂ / a) := by rw [heq]
        _ = n₂ := Nat.mul_div_cancel' h2'
    · intro b hb
      rw [Finset.mem_Icc] at hb
      refine ⟨a * b, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a b⟩,
        Nat.mul_div_cancel_left b (by omega)⟩
      · nlinarith [hb.1]
      · exact (Nat.le_div_iff_mul_le (by omega)).mp hb.2 |> fun h => by linarith
    · intro n hn
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
  rw [hdecomp]
  have hinner_le : ∀ a ∈ Finset.Icc 1 N,
      ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ) ≤
      ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    have hM1 : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    have hM_le : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
      exact_mod_cast Nat.div_mul_le_self N a
    have hlog_le : Real.log ((N / a : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (Nat.div_le_self N a))
    calc ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ)
        ≤ ∑ b ∈ Finset.Icc 1 (N / a), (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
          refine Finset.sum_le_sum fun b hb => ?_
          exact_mod_cast divisors_card_mul_le ha1 (Finset.mem_Icc.mp hb).1
      _ = (a.divisors.card : ℝ) * ∑ b ∈ Finset.Icc 1 (N / a), (b.divisors.card : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ (a.divisors.card : ℝ) * (((N / a : ℕ) : ℝ) * (1 + Real.log ((N / a : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hsum_d (N / a) hM1) (Nat.cast_nonneg _)
      _ ≤ (a.divisors.card : ℝ) * (((N : ℝ) / (a : ℝ)) * (1 + Real.log (N : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul hM_le (by linarith) (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr hM1)])
            (by positivity)
      _ = ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by ring
  calc ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 N, ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) :=
        Finset.sum_le_sum hinner_le
    _ = (∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 * ((N : ℝ) * (1 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hsum_d_div (by positivity)
    _ = (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by ring

/-- Tail bound `∑_{n ∈ Ioc X Y} n^(-α) * (log (2 * n))^k ≤ C(α, k) * X^(1 - α) * (log (2 * X))^k`
for every `α > 1` and `k : ℕ`, uniformly in `1 ≤ X` and `Y`. -/
lemma sum_rpow_mul_log_pow_le {α : ℝ} (hα : 1 < α) (k : ℕ) :
    ∃ C > 0, ∀ {X Y : ℕ}, 1 ≤ X →
      ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-α) * (Real.log (2 * (n : ℝ))) ^ k ≤
        C * (X : ℝ) ^ (1 - α) * (Real.log (2 * (X : ℝ))) ^ k := by
  set δ : ℝ := (α - 1) / 2
  set β : ℝ := (α + 1) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hβ : 1 < β := by dsimp only [β]; linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  set C₀ : ℝ := (2 : ℝ) ^ k * (1 + (2 * (k : ℝ) / δ) ^ k)
  refine ⟨C₀ / δ, by positivity, fun {X Y} hX => ?_⟩
  have hX0 : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog2X : (1 / 2 : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ (X : ℝ) := Nat.one_le_cast.mpr hX; linarith))
  -- Pointwise bound for `n > X`: `(log (2 * n))^k ≤ C₀ * (log (2 * X))^k * (n / X)^δ`
  have hpt : ∀ n ∈ Finset.Ioc X Y,
      (n : ℝ) ^ (-α) * (Real.log (2 * (n : ℝ))) ^ k ≤
        (C₀ * (Real.log (2 * (X : ℝ))) ^ k * (X : ℝ) ^ (-δ)) * (n : ℝ) ^ (-β) := by
    intro n hn
    have hXn : X < n := (Finset.mem_Ioc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    set t : ℝ := (n : ℝ) / (X : ℝ)
    have ht1 : 1 ≤ t := (one_le_div hX0).mpr (Nat.cast_le.mpr hXn.le)
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hlog_split : Real.log (2 * (n : ℝ)) = Real.log (2 * (X : ℝ)) + Real.log t := by
      rw [show 2 * (n : ℝ) = (2 * (X : ℝ)) * t by dsimp only [t]; field_simp [hX0.ne'],
        Real.log_mul (by positivity) ht0.ne']
    have hlogt_pow : (Real.log t) ^ k ≤ ((k : ℝ) / δ) ^ k * t ^ δ := by
      cases k with
      | zero => simp [Real.one_le_rpow ht1 hδ.le]
      | succ m =>
        have hkpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
        have hstep : Real.log t ≤ (((m + 1 : ℕ) : ℝ) / δ) * t ^ (δ / ((m + 1 : ℕ) : ℝ)) := by
          have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (δ / ((m + 1 : ℕ) : ℝ)))
          rw [Real.log_rpow ht0] at h1
          have h2 : (δ / ((m + 1 : ℕ) : ℝ)) * Real.log t ≤ t ^ (δ / ((m + 1 : ℕ) : ℝ)) := by linarith
          have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ) / δ)
          have hcancel : (((m + 1 : ℕ) : ℝ) / δ) * (δ / ((m + 1 : ℕ) : ℝ) * Real.log t) = Real.log t := by
            field_simp [hδ.ne', hkpos.ne']
          linarith
        have hpow := pow_le_pow_left₀ (Real.log_nonneg ht1) hstep (m + 1)
        rw [mul_pow, ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht0.le,
          div_mul_cancel₀ _ hkpos.ne'] at hpow
        exact hpow
    have hadd_pow : (Real.log (2 * (X : ℝ)) + Real.log t) ^ k ≤
        (2 : ℝ) ^ k * ((Real.log (2 * (X : ℝ))) ^ k + (Real.log t) ^ k) := by
      have ha : 0 ≤ Real.log (2 * (X : ℝ)) := by linarith
      have hb : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hmax : Real.log (2 * (X : ℝ)) + Real.log t ≤ 2 * max (Real.log (2 * (X : ℝ))) (Real.log t) := by
        linarith [le_max_left (Real.log (2 * (X : ℝ))) (Real.log t),
          le_max_right (Real.log (2 * (X : ℝ))) (Real.log t)]
      calc (Real.log (2 * (X : ℝ)) + Real.log t) ^ k
          ≤ (2 * max (Real.log (2 * (X : ℝ))) (Real.log t)) ^ k :=
            pow_le_pow_left₀ (by linarith) hmax k
        _ = (2 : ℝ) ^ k * (max (Real.log (2 * (X : ℝ))) (Real.log t)) ^ k := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ k * ((Real.log (2 * (X : ℝ))) ^ k + (Real.log t) ^ k) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rcases le_total (Real.log (2 * (X : ℝ))) (Real.log t) with hle | hge
            · rw [max_eq_right hle]; linarith [pow_nonneg ha k]
            · rw [max_eq_left hge]; linarith [pow_nonneg hb k]
    have h1_le_t : (1 : ℝ) ≤ t ^ δ := Real.one_le_rpow ht1 hδ.le
    have hlog2X_pow : 1 ≤ (2 * Real.log (2 * (X : ℝ))) ^ k := one_le_pow₀ (by linarith)
    have hlogt_rel : (Real.log t) ^ k ≤ (2 * (k : ℝ) / δ) ^ k * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ := by
      calc (Real.log t) ^ k
          ≤ ((k : ℝ) / δ) ^ k * t ^ δ := hlogt_pow
        _ ≤ ((k : ℝ) / δ) ^ k * t ^ δ * (2 * Real.log (2 * (X : ℝ))) ^ k :=
            le_mul_of_one_le_right (by positivity) hlog2X_pow
        _ = (2 * (k : ℝ) / δ) ^ k * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ := by
            rw [mul_pow, show (2 * (k : ℝ) / δ) ^ k = (2 : ℝ) ^ k * ((k : ℝ) / δ) ^ k by
              rw [← mul_pow]; congr 1; ring]
            ring
    have hlog_bd : (Real.log (2 * (n : ℝ))) ^ k ≤ C₀ * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ := by
      rw [hlog_split]
      have h1 : (Real.log (2 * (X : ℝ))) ^ k ≤ (Real.log (2 * (X : ℝ))) ^ k * t ^ δ :=
        le_mul_of_one_le_right (by positivity) h1_le_t
      calc (Real.log (2 * (X : ℝ)) + Real.log t) ^ k
          ≤ (2 : ℝ) ^ k * ((Real.log (2 * (X : ℝ))) ^ k + (Real.log t) ^ k) := hadd_pow
        _ ≤ (2 : ℝ) ^ k * ((Real.log (2 * (X : ℝ))) ^ k * t ^ δ +
            (2 * (k : ℝ) / δ) ^ k * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 hlogt_rel) (by positivity)
        _ = C₀ * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ := by dsimp only [C₀]; ring
    have hpow_comb : (n : ℝ) ^ (-α) * t ^ δ = (X : ℝ) ^ (-δ) * (n : ℝ) ^ (-β) := by
      dsimp only [t]
      rw [Real.div_rpow hn0.le hX0.le, div_eq_mul_inv, ← Real.rpow_neg hX0.le]
      calc (n : ℝ) ^ (-α) * ((n : ℝ) ^ δ * (X : ℝ) ^ (-δ))
          = (X : ℝ) ^ (-δ) * ((n : ℝ) ^ (-α) * (n : ℝ) ^ δ) := by ring
        _ = (X : ℝ) ^ (-δ) * (n : ℝ) ^ (-β) := by
            rw [← Real.rpow_add hn0]; congr 2; dsimp only [δ, β]; ring
    calc (n : ℝ) ^ (-α) * (Real.log (2 * (n : ℝ))) ^ k
        ≤ (n : ℝ) ^ (-α) * (C₀ * (Real.log (2 * (X : ℝ))) ^ k * t ^ δ) :=
          mul_le_mul_of_nonneg_left hlog_bd (Real.rpow_nonneg hn0.le _)
      _ = (C₀ * (Real.log (2 * (X : ℝ))) ^ k) * ((n : ℝ) ^ (-α) * t ^ δ) := by ring
      _ = (C₀ * (Real.log (2 * (X : ℝ))) ^ k * (X : ℝ) ^ (-δ)) * (n : ℝ) ^ (-β) := by
          rw [hpow_comb]; ring
  -- Bound `∑_{n ∈ Ioc X Y} n^(-β) ≤ X^(1 - β) / (β - 1) = X^(-δ) / δ` by telescoping!
  have hsum_beta : ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-β) ≤ (X : ℝ) ^ (-δ) / δ := by
    have hstep : ∀ n : ℕ, X < n →
        (n : ℝ) ^ (-β) ≤
          (((n - 1 : ℕ) : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) / δ := by
      intro n hn
      have hn0 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
      have hftc : ∫ x in ((n - 1 : ℕ) : ℝ)..(n : ℝ), x ^ (-β) =
          (((n - 1 : ℕ) : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) / δ := by
        have hd : ∀ x ∈ Set.uIcc ((n - 1 : ℕ) : ℝ) (n : ℝ),
            HasDerivAt (fun u : ℝ => -(u ^ (-δ) / δ)) (x ^ (-β)) x := by
          intro x hx
          rw [Set.uIcc_of_le hle] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
          have h := ((Real.hasDerivAt_rpow_const (p := -δ) (Or.inl hx0.ne')).div_const δ).neg
          refine h.congr_deriv ?_
          rw [show -δ - 1 = -β by dsimp only [δ, β]; ring]
          field_simp [hδ.ne']
        have hc : ContinuousOn (fun u : ℝ => u ^ (-β)) (Set.uIcc ((n - 1 : ℕ) : ℝ) (n : ℝ)) :=
          continuousOn_id.rpow_const fun x hx => by
            rw [Set.uIcc_of_le hle] at hx; exact Or.inl (lt_of_lt_of_le hn0 hx.1).ne'
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
        ring
      rw [← hftc]
      have hmono : ∫ _ in ((n - 1 : ℕ) : ℝ)..(n : ℝ), (n : ℝ) ^ (-β) ≤
          ∫ x in ((n - 1 : ℕ) : ℝ)..(n : ℝ), x ^ (-β) := by
        refine intervalIntegral.integral_mono_on hle intervalIntegrable_const ?_ fun x hx => ?_
        · exact (continuousOn_id.rpow_const fun u hu => Or.inl (lt_of_lt_of_le hn0 hu.1).ne').intervalIntegrable_of_Icc hle
        · exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hn0 hx.1) hx.2 (by linarith)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have hdiff : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
        have hcast : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) := Nat.cast_inj.mpr (by omega)
        push_cast at hcast; linarith
      rw [hdiff, one_mul] at hmono
      exact hmono
    by_cases hXY : Y ≤ X
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
    · push Not at hXY
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hXY)
      have htel : ∀ m : ℕ,
          ∑ n ∈ Finset.Ioc X (X + m), (((n - 1 : ℕ) : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) / δ =
          ((X : ℝ) ^ (-δ) - ((X + m : ℕ) : ℝ) ^ (-δ)) / δ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have hIoc : Finset.Ioc X (X + (m + 1)) = insert (X + (m + 1)) (Finset.Ioc X (X + m)) := by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          rw [hIoc, Finset.sum_insert (by simp), ih]
          have hsub : (X + (m + 1) - 1 : ℕ) = X + m := by omega
          rw [hsub]; ring
      calc ∑ n ∈ Finset.Ioc X (X + r), (n : ℝ) ^ (-β)
          ≤ ∑ n ∈ Finset.Ioc X (X + r), (((n - 1 : ℕ) : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) / δ :=
            Finset.sum_le_sum fun n hn => hstep n (Finset.mem_Ioc.mp hn).1
        _ = ((X : ℝ) ^ (-δ) - ((X + r : ℕ) : ℝ) ^ (-δ)) / δ := htel r
        _ ≤ (X : ℝ) ^ (-δ) / δ := div_le_div_of_nonneg_right
            (by linarith [Real.rpow_nonneg (Nat.cast_nonneg (X + r)) (-δ)]) hδ.le
  calc ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-α) * (Real.log (2 * (n : ℝ))) ^ k
      ≤ ∑ n ∈ Finset.Ioc X Y, (C₀ * (Real.log (2 * (X : ℝ))) ^ k * (X : ℝ) ^ (-δ)) * (n : ℝ) ^ (-β) :=
        Finset.sum_le_sum hpt
    _ = (C₀ * (Real.log (2 * (X : ℝ))) ^ k * (X : ℝ) ^ (-δ)) * ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-β) := by
        rw [← Finset.mul_sum]
    _ ≤ (C₀ * (Real.log (2 * (X : ℝ))) ^ k * (X : ℝ) ^ (-δ)) * ((X : ℝ) ^ (-δ) / δ) :=
        mul_le_mul_of_nonneg_left hsum_beta (by positivity)
    _ = (C₀ / δ) * ((X : ℝ) ^ (-δ) * (X : ℝ) ^ (-δ)) * (Real.log (2 * (X : ℝ))) ^ k := by ring
    _ = (C₀ / δ) * (X : ℝ) ^ (1 - α) * (Real.log (2 * (X : ℝ))) ^ k := by
        rw [← Real.rpow_add hX0, show -δ + -δ = 1 - α by dsimp only [δ]; ring]

/-- **Unconditional Large-Sieve Zero-Detecting Bound (Montgomery–Halász Engine)**:
for every fixed `σ > 1 / 2`, there exists `C > 0` such that for ALL `1 ≤ X ≤ Y`, `T ≥ 0`,
and EVERY finite `1`-well-spaced set `S : Finset ℂ` of points `ρ` (in particular, zeros of
`riemannZeta`) with `σ ≤ ρ.re`, `|ρ.im| ≤ T`, and
`1 / 2 ≤ ‖∑ n ∈ Finset.Ioc X Y, mollifiedCoeff X n * (n : ℂ) ^ (-ρ)‖`,
`(S.card : ℝ) ≤ C * (T + Y) * (Real.log (2 * Y)) ^ 4 * X ^ (1 - 2 * σ)`. -/
theorem zero_detecting_poly_count_le {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ C > 0, ∀ {X Y : ℕ} {T : ℝ}, 1 ≤ X → X ≤ Y → 0 ≤ T →
      ∀ (S : Finset ℂ),
      (∀ ρ ∈ S, σ ≤ ρ.re) →
      (∀ ρ ∈ S, |ρ.im| ≤ T) →
      (∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S, ρ₁ ≠ ρ₂ → 1 ≤ |ρ₁.im - ρ₂.im|) →
      (∀ ρ ∈ S, (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc X Y, mollifiedCoeff X n * (n : ℂ) ^ (-ρ)‖) →
      (S.card : ℝ) ≤ C * (T + (Y : ℝ)) * (Real.log (2 * (Y : ℝ))) ^ 4 * (X : ℝ) ^ (1 - 2 * σ) := by
  have h2σ : 1 < 2 * σ := by linarith
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := sum_rpow_mul_log_pow_le h2σ 2
  obtain ⟨C₄, hC₄_pos, hC₄⟩ := sum_rpow_mul_log_pow_le h2σ 4
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  -- Choose `C` large enough to absorb the explicit Abel summation + discrete large-sieve constants
  set K₀ : ℝ := 3 * (16 * Real.pi + 24)
  set A₁ : ℝ := 27 * (1 + (2 * σ + 2) * C₂)
  set A₂ : ℝ := 27 * (1 + 2 * σ * C₄)
  refine ⟨4 * K₀ * (A₁ + A₂), by positivity, fun {X Y T} hX hXY hT S hre him hsep hdet => ?_⟩
  have hX0 : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hY1 : 1 ≤ Y := le_trans hX hXY
  have hY0 : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog2X : (1 / 2 : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ (X : ℝ) := Nat.one_le_cast.mpr hX; linarith))
  have hlog2Y : (1 / 2 : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
    hlog2X.trans (Real.log_le_log (by positivity) (by have : (X : ℝ) ≤ (Y : ℝ) := Nat.cast_le.mpr hXY; linarith))
  -- Define the zero-detecting Dirichlet polynomial `F(s)` and its derivative `F'(s)`
  let c : ℕ → ℂ := fun n => if X < n then mollifiedCoeff X n else 0
  let F : ℂ → ℂ := fun s => ∑ n ∈ Finset.Ioc X Y, mollifiedCoeff X n * (n : ℂ) ^ (-s)
  let F' : ℂ → ℂ := fun s => ∑ n ∈ Finset.Ioc X Y,
    (-(Real.log (n : ℝ) : ℂ)) * mollifiedCoeff X n * (n : ℂ) ^ (-s)
  -- Step 1: Horizontal FTC bound for each `ρ ∈ S`:
  -- `‖F(ρ)‖^2 ≤ 2 * ∫_{Ioi σ} ‖F(u + I*ρ.im)‖ * ‖F'(u + I*ρ.im)‖ du`
  have hhoriz : ∀ ρ ∈ S,
      ‖F ρ‖ ^ 2 ≤ 2 * ∫ u in Ioi σ, ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ *
        ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ := by
    intro ρ hρ
    set γ : ℝ := ρ.im
    have hρ_eq : ρ = ((ρ.re : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
      dsimp only [γ]; rw [mul_comm, Complex.re_add_im]
    let g : ℝ → ℂ := fun u => F ((u : ℂ) + Complex.I * (γ : ℂ))
    let g' : ℝ → ℂ := fun u => F' ((u : ℂ) + Complex.I * (γ : ℂ))
    have hg_deriv : ∀ u : ℝ, HasDerivAt g (g' u) u := by
      intro u
      dsimp only [g, g', F, F']
      have hterm : ∀ n ∈ Finset.Ioc X Y,
          HasDerivAt (fun x : ℝ => mollifiedCoeff X n * (n : ℂ) ^ (-((x : ℂ) + Complex.I * (γ : ℂ))))
            ((-(Real.log (n : ℝ) : ℂ)) * mollifiedCoeff X n *
              (n : ℂ) ^ (-((u : ℂ) + Complex.I * (γ : ℂ)))) u := by
        intro n hn
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hfun : (fun x : ℝ => mollifiedCoeff X n * (n : ℂ) ^ (-((x : ℂ) + Complex.I * (γ : ℂ)))) =
            fun x : ℝ => mollifiedCoeff X n * Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (γ : ℂ)))) := by
          funext x
          rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
        rw [hfun]
        have hlin : HasDerivAt (fun x : ℝ => (Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (γ : ℂ))))
            (-(Real.log (n : ℝ) : ℂ)) u := by
          have hid := ((hasDerivAt_id u).ofReal_comp.add_const (Complex.I * (γ : ℂ))).neg.const_mul (Real.log (n : ℝ) : ℂ)
          refine hid.congr_deriv ?_; simp only [Complex.ofReal_one]; ring
        refine (hlin.cexp.const_mul (mollifiedCoeff X n)).congr_deriv ?_
        rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]; ring
      exact HasDerivAt.fun_sum hterm
    have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg_deriv u).continuousAt
    have hg'_cont : Continuous g' := by
      dsimp only [g', F']
      refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hfun : (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) + Complex.I * (γ : ℂ)))) =
          fun x : ℝ => Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (γ : ℂ)))) := by
        funext x
        rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      rw [hfun]
      exact Complex.continuous_exp.comp
        (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).neg))
    -- Exponential decay of `g u` and `g' u` as `u → ∞` (every `n ∈ Ioc X Y` has `n ≥ 2`!)
    have hdecay_g : ∀ u : ℝ, 0 ≤ u → ‖g u‖ ≤ (∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖) * (2 : ℝ) ^ (-u) := by
      intro u hu
      dsimp only [g, F]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2_nat : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2_nat
      rw [norm_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), show (-((u : ℂ) + Complex.I * (γ : ℂ))).re = -u by simp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)) (norm_nonneg _)
    have hdecay_g' : ∀ u : ℝ, 0 ≤ u →
        ‖g' u‖ ≤ (∑ n ∈ Finset.Ioc X Y, Real.log (n : ℝ) * ‖mollifiedCoeff X n‖) * (2 : ℝ) ^ (-u) := by
      intro u hu
      dsimp only [g', F']
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2_nat : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2_nat
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg (by linarith)), ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), show (-((u : ℂ) + Complex.I * (γ : ℂ))).re = -u by simp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)) (by positivity)
    have hint_prod : IntegrableOn (fun u : ℝ => ‖g u‖ * ‖g' u‖) (Ioi σ) := by
      set B₁ := ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖
      set B₂ := ∑ n ∈ Finset.Ioc X Y, Real.log (n : ℝ) * ‖mollifiedCoeff X n‖
      have hexp_int : IntegrableOn (fun u : ℝ => (B₁ * B₂) * Real.exp (-(2 * Real.log 2) * u)) (Ioi σ) :=
        (integrableOn_exp_mul_Ioi (by linarith : -(2 * Real.log 2) < 0) σ).const_mul (B₁ * B₂)
      refine hexp_int.mono' ((hg_cont.norm.mul hg'_cont.norm).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
      rw [Set.mem_Ioi] at hu
      have hu0 : 0 ≤ u := by linarith
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖g u‖ * ‖g' u‖
          ≤ (B₁ * (2 : ℝ) ^ (-u)) * (B₂ * (2 : ℝ) ^ (-u)) :=
            mul_le_mul (hdecay_g u hu0) (hdecay_g' u hu0) (norm_nonneg _) (by positivity)
        _ = (B₁ * B₂) * Real.exp (-(2 * Real.log 2) * u) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
              show B₁ * Real.exp (Real.log 2 * -u) * (B₂ * Real.exp (Real.log 2 * -u)) =
                (B₁ * B₂) * (Real.exp (Real.log 2 * -u) * Real.exp (Real.log 2 * -u)) by ring,
              ← Real.exp_add]
            congr 2; ring
    -- FTC on `[ρ.re, M]` and let `M → ∞`
    have hM_le : ∀ M : ℝ, ρ.re ≤ M →
        ‖g ρ.re‖ ^ 2 - ‖g M‖ ^ 2 ≤ 2 * ∫ u in σ..M, ‖g u‖ * ‖g' u‖ := by
      intro M hM
      have hderiv_sq : ∀ u : ℝ, HasDerivAt (fun x : ℝ => ‖g x‖ ^ 2) (2 * (g' u * star (g u)).re) u := by
        intro u
        have hf := hg_deriv u
        have hstar : HasDerivAt (fun x : ℝ => star (g x)) (star (g' u)) u :=
          Complex.conjCLE.hasFDerivAt.comp_hasDerivAt u hf
        have hre' : HasDerivAt (fun x : ℝ => (g x * star (g x)).re)
            (g' u * star (g u) + g u * star (g' u)).re u :=
          Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hf.mul hstar)
        have hfun : (fun x : ℝ => (g x * star (g x)).re) = fun x : ℝ => ‖g x‖ ^ 2 := by
          funext x; rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        rw [hfun] at hre'
        refine hre'.congr_deriv ?_
        rw [Complex.add_re]
        have h1 : star (g' u * star (g u)) = g u * star (g' u) := by rw [star_mul', star_star, mul_comm]
        rw [← h1, Complex.star_def, Complex.conj_re]; ring
      have hc_dsq : Continuous (fun u : ℝ => 2 * (g' u * star (g u)).re) :=
        continuous_const.mul (Complex.continuous_re.comp
          (hg'_cont.mul (Complex.conjCLE.continuous.comp hg_cont)))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hderiv_sq u) (hc_dsq.intervalIntegrable ρ.re M)
      have h1 : ‖g ρ.re‖ ^ 2 - ‖g M‖ ^ 2 = -(∫ u in ρ.re..M, 2 * (g' u * star (g u)).re) := by
        linarith
      rw [h1]
      calc -(∫ u in ρ.re..M, 2 * (g' u * star (g u)).re)
          ≤ |∫ u in ρ.re..M, 2 * (g' u * star (g u)).re| := neg_le_abs _
        _ ≤ ∫ u in ρ.re..M, |2 * (g' u * star (g u)).re| :=
            intervalIntegral.abs_integral_le_integral_abs hM
        _ ≤ ∫ u in ρ.re..M, 2 * (‖g u‖ * ‖g' u‖) := by
            refine intervalIntegral.integral_mono_on hM (hc_dsq.abs.intervalIntegrable _ _)
              ((continuous_const.mul (hg_cont.norm.mul hg'_cont.norm)).intervalIntegrable _ _) fun u _ => ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            have hre_le : |(g' u * star (g u)).re| ≤ ‖g u‖ * ‖g' u‖ :=
              (Complex.abs_re_le_norm _).trans (by rw [norm_mul, norm_star, mul_comm])
            linarith
        _ ≤ ∫ u in σ..M, 2 * (‖g u‖ * ‖g' u‖) := by
            have hσM : σ ≤ M := (hre ρ hρ).trans hM
            rw [intervalIntegral.integral_of_le hM, intervalIntegral.integral_of_le hσM]
            exact setIntegral_mono_set
              ((intervalIntegrable_iff_integrableOn_Ioc_of_le hσM).mp
                ((continuous_const.mul (hg_cont.norm.mul hg'_cont.norm)).intervalIntegrable _ _))
              (ae_of_all _ fun _ => by positivity)
              (Eventually.of_forall (Set.Ioc_subset_Ioc_left (hre ρ hρ)))
        _ = 2 * ∫ u in σ..M, ‖g u‖ * ‖g' u‖ := intervalIntegral.integral_const_mul _ _
    have htend_g : Tendsto (fun M : ℝ => ‖g M‖ ^ 2) atTop (nhds 0) := by
      set B₁ := ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖
      have h0 : Tendsto (fun M : ℝ => (B₁ * Real.exp (-Real.log 2 * M)) ^ 2) atTop (nhds 0) := by
        have h1 : Tendsto (fun M : ℝ => Real.exp (-Real.log 2 * M)) atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simpa using (h1.const_mul B₁).pow 2
      refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ h0
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
      have h1 := hdecay_g M hM
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * -M = -Real.log 2 * M by ring] at h1
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have htendL : Tendsto (fun M : ℝ => ‖g ρ.re‖ ^ 2 - ‖g M‖ ^ 2) atTop (nhds (‖g ρ.re‖ ^ 2)) := by
      simpa using tendsto_const_nhds.sub htend_g
    have htendR : Tendsto (fun M : ℝ => 2 * ∫ u in σ..M, ‖g u‖ * ‖g' u‖) atTop
        (nhds (2 * ∫ u in Ioi σ, ‖g u‖ * ‖g' u‖)) :=
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi σ hint_prod tendsto_id).const_mul 2
    have hle := le_of_tendsto_of_tendsto htendL htendR (eventually_atTop.mpr ⟨ρ.re, hM_le⟩)
    simpa [g, ← hρ_eq] using hle
  -- Step 2: Apply AM-GM `2 * a * b ≤ α₀ * a^2 + α₀⁻¹ * b^2` with `α₀ = Real.log (2 * Y)` and sum over `ρ ∈ S`!
  set α₀ : ℝ := Real.log (2 * (Y : ℝ))
  have hα₀_pos : 0 < α₀ := by linarith
  -- Integrability of `∑_{ρ ∈ S} ‖F(u + I * ρ.im)‖^2` and `‖F'(u + I * ρ.im)‖^2` on `Ioi σ`
  have hint_F_sq : ∀ ρ ∈ S, IntegrableOn (fun u : ℝ => ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) (Ioi σ) := by
    intro ρ _
    set B₁ := ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖
    have hcont : Continuous (fun u : ℝ => ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) := by
      refine (continuous_finsetSum _ fun n hn => continuous_const.mul ?_).norm.pow 2
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hfun : (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) =
          fun x : ℝ => Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) := by
        funext x; rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      rw [hfun]
      exact Complex.continuous_exp.comp
        (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).neg))
    refine ((integrableOn_exp_mul_Ioi (by linarith : -(2 * Real.log 2) < 0) σ).const_mul (B₁ ^ 2)).mono'
      (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    rw [Set.mem_Ioi] at hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ≤ B₁ * Real.exp (-Real.log 2 * u) := by
      dsimp only [F, B₁]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2_nat : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2_nat
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
        show (-((u : ℂ) + Complex.I * (ρ.im : ℂ))).re = -u by simp]
      have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith : -u ≤ 0)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), show Real.log 2 * -u = -Real.log 2 * u by ring] at h2
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    calc ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2
        ≤ (B₁ * Real.exp (-Real.log 2 * u)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = B₁ ^ 2 * Real.exp (-(2 * Real.log 2) * u) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hint_F'_sq : ∀ ρ ∈ S, IntegrableOn (fun u : ℝ => ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) (Ioi σ) := by
    intro ρ _
    set B₂ := ∑ n ∈ Finset.Ioc X Y, Real.log (n : ℝ) * ‖mollifiedCoeff X n‖
    have hcont : Continuous (fun u : ℝ => ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) := by
      refine (continuous_finsetSum _ fun n hn => continuous_const.mul ?_).norm.pow 2
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
      have hfun : (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) =
          fun x : ℝ => Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) := by
        funext x; rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      rw [hfun]
      exact Complex.continuous_exp.comp
        (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).neg))
    refine ((integrableOn_exp_mul_Ioi (by linarith : -(2 * Real.log 2) < 0) σ).const_mul (B₂ ^ 2)).mono'
      (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    rw [Set.mem_Ioi] at hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ≤ B₂ * Real.exp (-Real.log 2 * u) := by
      dsimp only [F', B₂]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn2_nat : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2_nat
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg (by linarith)), ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
        show (-((u : ℂ) + Complex.I * (ρ.im : ℂ))).re = -u by simp]
      have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith : -u ≤ 0)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), show Real.log 2 * -u = -Real.log 2 * u by ring] at h2
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2
        ≤ (B₂ * Real.exp (-Real.log 2 * u)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = B₂ ^ 2 * Real.exp (-(2 * Real.log 2) * u) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  -- Step 3: For each fixed `u > σ`, apply `dirichletPoly_discrete_large_sieve` with `δ = 1`!
  have hls_F : ∀ u : ℝ,
      ∑ ρ ∈ S, ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) := by
    intro u
    let au : ℕ → ℂ := fun n => if X < n then mollifiedCoeff X n * (n : ℂ) ^ (-(u : ℂ)) else 0
    have hrew : ∀ ρ ∈ S, F ((u : ℂ) + Complex.I * (ρ.im : ℂ)) =
        dirichletPoly au Y (Complex.I * (ρ.im : ℂ)) := by
      intro ρ _
      dsimp only [F, dirichletPoly, au]
      have hIoc : Finset.Ioc X Y = (Finset.Icc 1 Y).filter (fun n => X < n) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hIoc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      by_cases hXn : X < n
      · rw [if_pos hXn, if_pos hXn]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [mul_assoc, ← Complex.cpow_add _ _ hnC]
        congr 2; ring
      · rw [if_neg hXn, if_neg hXn, zero_mul]
    rw [Finset.sum_congr rfl fun ρ hρ => by rw [hrew ρ hρ]]
    have hls := dirichletPoly_discrete_large_sieve S (fun ρ : ℂ => ρ.im) hY1 hT zero_lt_one him hsep au
    have hsum_au : ∑ n ∈ Finset.Icc 1 Y, ‖au n‖ ^ 2 =
        ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) := by
      have hIoc : Finset.Ioc X Y = (Finset.Icc 1 Y).filter (fun n => X < n) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hIoc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      dsimp only [au]
      by_cases hXn : X < n
      · rw [if_pos hXn, if_pos hXn, norm_mul, mul_pow, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega)),
          show (-(u : ℂ)).re = -u by simp, ← Real.rpow_natCast ((n : ℝ) ^ (-u)) 2,
          ← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 2; ring
      · rw [if_neg hXn, if_neg hXn]; simp
    rw [hsum_au] at hls
    have h1log : (1 : ℝ)⁻¹ + Real.log (2 * (Y : ℝ)) ≤ 3 * Real.log (2 * (Y : ℝ)) := by
      rw [inv_one]; linarith
    refine hls.trans ?_
    have hnn : 0 ≤ ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hK_le : (16 * Real.pi + 24) * (T + (Y : ℝ)) * ((1 : ℝ)⁻¹ + Real.log (2 * (Y : ℝ))) ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) := by
      dsimp only [K₀]
      have hmul := mul_le_mul_of_nonneg_left h1log (by positivity : 0 ≤ (16 * Real.pi + 24) * (T + (Y : ℝ)))
      linarith
    exact mul_le_mul_of_nonneg_right hK_le hnn
  have hls_F' : ∀ u : ℝ,
      ∑ ρ ∈ S, ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, (Real.log (n : ℝ)) ^ 2 * ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) := by
    intro u
    let bu : ℕ → ℂ := fun n => if X < n then
      (-(Real.log (n : ℝ) : ℂ)) * mollifiedCoeff X n * (n : ℂ) ^ (-(u : ℂ)) else 0
    have hrew : ∀ ρ ∈ S, F' ((u : ℂ) + Complex.I * (ρ.im : ℂ)) =
        dirichletPoly bu Y (Complex.I * (ρ.im : ℂ)) := by
      intro ρ _
      dsimp only [F', dirichletPoly, bu]
      have hIoc : Finset.Ioc X Y = (Finset.Icc 1 Y).filter (fun n => X < n) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hIoc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      by_cases hXn : X < n
      · rw [if_pos hXn, if_pos hXn]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [mul_assoc ((-(Real.log (n : ℝ) : ℂ)) * mollifiedCoeff X n), ← Complex.cpow_add _ _ hnC]
        congr 2; ring
      · rw [if_neg hXn, if_neg hXn, zero_mul]
    rw [Finset.sum_congr rfl fun ρ hρ => by rw [hrew ρ hρ]]
    have hls := dirichletPoly_discrete_large_sieve S (fun ρ : ℂ => ρ.im) hY1 hT zero_lt_one him hsep bu
    have hsum_bu : ∑ n ∈ Finset.Icc 1 Y, ‖bu n‖ ^ 2 =
        ∑ n ∈ Finset.Ioc X Y, (Real.log (n : ℝ)) ^ 2 * ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) := by
      have hIoc : Finset.Ioc X Y = (Finset.Icc 1 Y).filter (fun n => X < n) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hIoc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      dsimp only [bu]
      by_cases hXn : X < n
      · have hn2 : 2 ≤ n := by omega
        rw [if_pos hXn, if_pos hXn, norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (by omega))),
          mul_pow, mul_pow, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega)),
          show (-(u : ℂ)).re = -u by simp, ← Real.rpow_natCast ((n : ℝ) ^ (-u)) 2,
          ← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 2; ring
      · rw [if_neg hXn, if_neg hXn]; simp
    rw [hsum_bu] at hls
    have h1log : (1 : ℝ)⁻¹ + Real.log (2 * (Y : ℝ)) ≤ 3 * Real.log (2 * (Y : ℝ)) := by
      rw [inv_one]; linarith
    refine hls.trans ?_
    have hnn : 0 ≤ ∑ n ∈ Finset.Ioc X Y, (Real.log (n : ℝ)) ^ 2 * ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hK_le : (16 * Real.pi + 24) * (T + (Y : ℝ)) * ((1 : ℝ)⁻¹ + Real.log (2 * (Y : ℝ))) ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) := by
      dsimp only [K₀]
      have hmul := mul_le_mul_of_nonneg_left h1log (by positivity : 0 ≤ (16 * Real.pi + 24) * (T + (Y : ℝ)))
      linarith
    exact mul_le_mul_of_nonneg_right hK_le hnn
  -- Step 4: Integrate `u` over `(σ, ∞)` using `∫_σ^∞ n^(-2u) du = n^(-2σ) / (2 * log n)`!
  have hint_n_rpow : ∀ n ∈ Finset.Ioc X Y,
      ∫ u in Ioi σ, (n : ℝ) ^ (-2 * u) = (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) := by
    intro n hn
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hrew : (fun u : ℝ => (n : ℝ) ^ (-2 * u)) = fun u : ℝ => Real.exp (-(2 * Real.log (n : ℝ)) * u) := by
      funext u; rw [Real.rpow_def_of_pos hn0]; congr 1; ring
    rw [hrew, integral_exp_mul_Ioi (by linarith : -(2 * Real.log (n : ℝ)) < 0) σ]
    rw [Real.rpow_def_of_pos hn0, show Real.log (n : ℝ) * (-2 * σ) = -(2 * Real.log (n : ℝ)) * σ by ring]
    ring
  have hsum_F_bd : ∑ ρ ∈ S, ‖F ρ‖ ^ 2 ≤
      K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
        (α₀ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ))) +
         α₀⁻¹ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ))) := by
    -- Sum `hhoriz`, apply `2 * a * b ≤ α₀ * a^2 + α₀⁻¹ * b^2`, swap `∑_{ρ ∈ S}` and `∫_{Ioi σ}`
    have h1 : ∑ ρ ∈ S, ‖F ρ‖ ^ 2 ≤
        α₀ * (∫ u in Ioi σ, ∑ ρ ∈ S, ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) +
        α₀⁻¹ * (∫ u in Ioi σ, ∑ ρ ∈ S, ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2) := by
      rw [MeasureTheory.integral_finsetSum S hint_F_sq, MeasureTheory.integral_finsetSum S hint_F'_sq,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ρ hρ => (hhoriz ρ hρ).trans ?_
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_add ((hint_F_sq ρ hρ).const_mul α₀) ((hint_F'_sq ρ hρ).const_mul α₀⁻¹)]
      have hFc : Continuous (fun u : ℝ => F ((u : ℂ) + Complex.I * (ρ.im : ℂ))) := by
        dsimp only [F]
        refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
        have hfun : (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) =
            fun x : ℝ => Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) := by
          funext x; rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
        rw [hfun]
        exact Complex.continuous_exp.comp
          (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).neg))
      have hF'c : Continuous (fun u : ℝ => F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))) := by
        dsimp only [F']
        refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega)
        have hfun : (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) =
            fun x : ℝ => Complex.exp ((Real.log (n : ℝ) : ℂ) * (-((x : ℂ) + Complex.I * (ρ.im : ℂ)))) := by
          funext x; rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
        rw [hfun]
        exact Complex.continuous_exp.comp
          (continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).neg))
      refine setIntegral_mono_on ?_ (((hint_F_sq ρ hρ).const_mul α₀).add ((hint_F'_sq ρ hρ).const_mul α₀⁻¹))
        measurableSet_Ioi fun u _ => ?_
      · -- Integrability of `2 * ‖F‖ * ‖F'‖` from AM-GM dominance
        refine (((hint_F_sq ρ hρ).const_mul α₀).add ((hint_F'_sq ρ hρ).const_mul α₀⁻¹)).mono'
          ((continuous_const.mul (hFc.norm.mul hF'c.norm)).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
        refine ae_of_all _ fun u => ?_
        rw [Real.norm_of_nonneg (by positivity)]
        have hsq := sq_nonneg (Real.sqrt α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ -
          ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ / Real.sqrt α₀)
        have hne : Real.sqrt α₀ ≠ 0 := (Real.sqrt_pos.mpr hα₀_pos).ne'
        have hexp : (Real.sqrt α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ -
            ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ / Real.sqrt α₀) ^ 2 =
            α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 -
            2 * (‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖) +
            α₀⁻¹ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 := by
          field_simp [hne]; rw [Real.sq_sqrt hα₀_pos.le]; field_simp [hα₀_pos.ne']; ring
        show 2 * (‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖) ≤
          α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 +
          α₀⁻¹ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2
        linarith
      · have hsq := sq_nonneg (Real.sqrt α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ -
          ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ / Real.sqrt α₀)
        have hne : Real.sqrt α₀ ≠ 0 := (Real.sqrt_pos.mpr hα₀_pos).ne'
        have hexp : (Real.sqrt α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ -
            ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ / Real.sqrt α₀) ^ 2 =
            α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 -
            2 * (‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖) +
            α₀⁻¹ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 := by
          field_simp [hne]; rw [Real.sq_sqrt hα₀_pos.le]; field_simp [hα₀_pos.ne']; ring
        show 2 * (‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖) ≤
          α₀ * ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 +
          α₀⁻¹ * ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2
        linarith
    have hint_n_int : ∀ n ∈ Finset.Ioc X Y, IntegrableOn (fun u : ℝ => (n : ℝ) ^ (-2 * u)) (Ioi σ) := by
      intro n hn
      have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hrew : (fun u : ℝ => (n : ℝ) ^ (-2 * u)) = fun u : ℝ => Real.exp (-(2 * Real.log (n : ℝ)) * u) := by
        funext u; rw [Real.rpow_def_of_pos hn0]; congr 1; ring
      rw [hrew]
      exact integrableOn_exp_mul_Ioi (by linarith) σ
    have hI1 : ∫ u in Ioi σ, ∑ ρ ∈ S, ‖F ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) := by
      have hdom : IntegrableOn (fun u : ℝ => K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u)) (Ioi σ) :=
        (integrable_finsetSum _ fun n hn => (hint_n_int n hn).const_mul _).const_mul _
      have hmono := setIntegral_mono_on (integrable_finsetSum S hint_F_sq) hdom measurableSet_Ioi fun u _ => hls_F u
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ fun n hn => (hint_n_int n hn).const_mul _] at hmono
      refine hmono.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity))
      rw [MeasureTheory.integral_const_mul, hint_n_rpow n hn]
      have hmc := pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedCoeff_le_divisors X n) 2
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (show 1 < n by omega))
      calc ‖mollifiedCoeff X n‖ ^ 2 * ((n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)))
          ≤ (n.divisors.card : ℝ) ^ 2 * ((n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hmc (by positivity)
        _ = (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) := by ring
    have hI2 : ∫ u in Ioi σ, ∑ ρ ∈ S, ‖F' ((u : ℂ) + Complex.I * (ρ.im : ℂ))‖ ^ 2 ≤
        K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ) := by
      have hdom : IntegrableOn (fun u : ℝ => K₀ * (T + (Y : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ Finset.Ioc X Y, (Real.log (n : ℝ)) ^ 2 * ‖mollifiedCoeff X n‖ ^ 2 * (n : ℝ) ^ (-2 * u)) (Ioi σ) :=
        (integrable_finsetSum _ fun n hn => (hint_n_int n hn).const_mul _).const_mul _
      have hmono := setIntegral_mono_on (integrable_finsetSum S hint_F'_sq) hdom measurableSet_Ioi fun u _ => hls_F' u
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ fun n hn => (hint_n_int n hn).const_mul _] at hmono
      refine hmono.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity))
      rw [MeasureTheory.integral_const_mul, hint_n_rpow n hn]
      have hmc := pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedCoeff_le_divisors X n) 2
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (show 1 < n by omega))
      have hsimp : (Real.log (n : ℝ)) ^ 2 * ‖mollifiedCoeff X n‖ ^ 2 * ((n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ))) =
          ‖mollifiedCoeff X n‖ ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ) := by
        field_simp [hlogn.ne']
      rw [hsimp]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmc (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hmul1 := mul_le_mul_of_nonneg_left hI1 hα₀_pos.le
    have hmul2 := mul_le_mul_of_nonneg_left hI2 (inv_nonneg.mpr hα₀_pos.le)
    linarith
  -- Step 5: Abel summation for BOTH divisor-squared tails `I₁` and `I₂`!
  let D2 : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 n, (k.divisors.card : ℝ) ^ 2
  have hD2_bd : ∀ n : ℕ, 2 ≤ n → D2 n ≤ 27 * (n : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
    intro n hn
    have h1 := sum_divisors_card_sq_le (show 1 ≤ n by omega)
    have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) :=
      hlog2.trans (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hn))
    have h1log : 1 + Real.log (n : ℝ) ≤ 3 * Real.log (n : ℝ) := by linarith
    calc D2 n ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 3 := h1
      _ ≤ (n : ℝ) * (3 * Real.log (n : ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1log 3) (Nat.cast_nonneg n)
      _ = 27 * (n : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring
  -- Generic finite Abel summation identity on `Finset.Ioc X Y` for any weight `w : ℕ → ℝ`:
  have habel : ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) →
      ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * w n ≤
        D2 Y * w Y + ∑ n ∈ Finset.Ioc X Y, D2 n * max 0 (w n - w (n + 1)) := by
    intro w hw
    by_cases hXY' : Y ≤ X
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, Finset.sum_empty, add_zero]
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hw Y)
    · push Not at hXY'
      -- Prove by induction on `r` where `Y = X + 1 + r`
      have hgen : ∀ r : ℕ,
          ∑ n ∈ Finset.Ioc X (X + 1 + r), (n.divisors.card : ℝ) ^ 2 * w n =
            D2 (X + 1 + r) * w (X + 1 + r) - D2 X * w (X + 1) +
            ∑ n ∈ Finset.Ioc X (X + r), D2 n * (w n - w (n + 1)) := by
        intro r
        induction r with
        | zero =>
          have hI1 : Finset.Ioc X (X + 1) = {X + 1} := by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
          have hI0 : Finset.Ioc X X = ∅ := Finset.Ioc_eq_empty (by omega)
          rw [add_zero, add_zero, hI1, hI0, Finset.sum_singleton, Finset.sum_empty, add_zero]
          have hD_step : D2 (X + 1) = D2 X + ((X + 1).divisors.card : ℝ) ^ 2 := by
            dsimp only [D2]
            have hIcc : Finset.Icc 1 (X + 1) = insert (X + 1) (Finset.Icc 1 X) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]; ring
          rw [hD_step]; ring
        | succ r ih =>
          have hI1 : Finset.Ioc X (X + 1 + (r + 1)) = insert (X + 1 + (r + 1)) (Finset.Ioc X (X + 1 + r)) := by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          have hI2 : Finset.Ioc X (X + (r + 1)) = insert (X + 1 + r) (Finset.Ioc X (X + r)) := by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          rw [hI1, Finset.sum_insert (by simp), ih, hI2, Finset.sum_insert (by simp)]
          have hD_step : D2 (X + 1 + (r + 1)) = D2 (X + 1 + r) + ((X + 1 + (r + 1)).divisors.card : ℝ) ^ 2 := by
            dsimp only [D2]
            have hIcc : Finset.Icc 1 (X + 1 + (r + 1)) = insert (X + 1 + (r + 1)) (Finset.Icc 1 (X + 1 + r)) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]; ring
          have hidx : X + 1 + r + 1 = X + 1 + (r + 1) := by omega
          rw [hD_step, hidx]; ring
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show X + 1 ≤ Y by omega)
      rw [hgen r]
      have hDX_nn : 0 ≤ D2 X * w (X + 1) :=
        mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (hw (X + 1))
      have hsub : Finset.Ioc X (X + r) ⊆ Finset.Ioc X (X + 1 + r) :=
        Finset.Ioc_subset_Ioc_right (by omega)
      have hsum_le : ∑ n ∈ Finset.Ioc X (X + r), D2 n * (w n - w (n + 1)) ≤
          ∑ n ∈ Finset.Ioc X (X + 1 + r), D2 n * max 0 (w n - w (n + 1)) := by
        refine (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) (w n - w (n + 1)))
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_max_left _ _)
      linarith
  -- Bound the elementary difference `n^(-2σ) - (n+1)^(-2σ) ≤ 2σ * n^(-2σ - 1)` for `n ≥ 1`
  have hrpow_diff : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (-2 * σ) - ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) ≤ 2 * σ * (n : ℝ) ^ (-2 * σ - 1) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ n)
    have hftc : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), 2 * σ * x ^ (-2 * σ - 1) =
        (n : ℝ) ^ (-2 * σ) - ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) := by
      have hd : ∀ x ∈ Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ),
          HasDerivAt (fun u : ℝ => -(u ^ (-2 * σ))) (2 * σ * x ^ (-2 * σ - 1)) x := by
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
        have h := (Real.hasDerivAt_rpow_const (p := -2 * σ) (Or.inl hx0.ne')).neg
        refine h.congr_deriv ?_; ring
      have hc : ContinuousOn (fun u : ℝ => 2 * σ * u ^ (-2 * σ - 1)) (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
        continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => by
          rw [Set.uIcc_of_le hle] at hx; exact Or.inl (lt_of_lt_of_le hn0 hx.1).ne')
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
      ring
    rw [← hftc]
    have hmono : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), 2 * σ * x ^ (-2 * σ - 1) ≤
        ∫ _ in (n : ℝ)..((n + 1 : ℕ) : ℝ), 2 * σ * (n : ℝ) ^ (-2 * σ - 1) := by
      refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const fun x hx => ?_
      · exact (continuousOn_const.mul (continuousOn_id.rpow_const fun u hu =>
          Or.inl (lt_of_lt_of_le hn0 hu.1).ne')).intervalIntegrable_of_Icc hle
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hn0 hx.1 (by linarith)) (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hdiff : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    rw [hdiff, one_mul] at hmono
    exact hmono
  -- Bound `I₁`: `∑_{n ∈ Ioc X Y} d(n)^2 * n^(-2σ) / (2 * log n) ≤ A₁ * X^(1 - 2σ) * (log(2*X))^2`
  have hI1_tail : ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) ≤
      A₁ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
    by_cases hXY' : Y ≤ X
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
    · push Not at hXY'
      have hY2 : 2 ≤ Y := by omega
      let w₁ : ℕ → ℝ := fun n => if 2 ≤ n then (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) else 0
      have hw₁_nn : ∀ n, 0 ≤ w₁ n := fun n => by
        dsimp only [w₁]; split_ifs with h
        · have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
          positivity
        · exact le_rfl
      have hrew : ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) =
          ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * w₁ n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        dsimp only [w₁]; rw [if_pos hn2]; ring
      rw [hrew]
      refine (habel w₁ hw₁_nn).trans ?_
      -- Boundary term `D2 Y * w₁ Y`
      have hbd_Y : D2 Y * w₁ Y ≤ 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
        dsimp only [w₁]; rw [if_pos hY2]
        have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
        have hlogY_le : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
          Real.log_le_log hY0 (by linarith)
        have hDY := hD2_bd Y hY2
        have hYpow : (Y : ℝ) * (Y : ℝ) ^ (-2 * σ) = (Y : ℝ) ^ (1 - 2 * σ) := by
          rw [show (Y : ℝ) * (Y : ℝ) ^ (-2 * σ) = (Y : ℝ) ^ (1 : ℝ) * (Y : ℝ) ^ (-2 * σ) by rw [Real.rpow_one],
            ← Real.rpow_add hY0]
          congr 1; ring
        have hYX : (Y : ℝ) ^ (1 - 2 * σ) ≤ (X : ℝ) ^ (1 - 2 * σ) :=
          Real.rpow_le_rpow_of_nonpos hX0 (Nat.cast_le.mpr hXY) (by linarith)
        calc D2 Y * ((Y : ℝ) ^ (-2 * σ) / (2 * Real.log (Y : ℝ)))
            ≤ (27 * (Y : ℝ) * (Real.log (Y : ℝ)) ^ 3) * ((Y : ℝ) ^ (-2 * σ) / (2 * Real.log (Y : ℝ))) :=
              mul_le_mul_of_nonneg_right hDY (by positivity)
          _ = (27 / 2) * ((Y : ℝ) * (Y : ℝ) ^ (-2 * σ)) * (Real.log (Y : ℝ)) ^ 2 := by
              field_simp [hlogY.ne']
          _ ≤ 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
              rw [hYpow]
              have hsq := pow_le_pow_left₀ hlogY.le hlogY_le 2
              have h1 := mul_le_mul hYX hsq (sq_nonneg _) (Real.rpow_nonneg hX0.le _)
              have hnn := mul_nonneg (Real.rpow_nonneg hX0.le (1 - 2 * σ)) (sq_nonneg (Real.log (2 * (Y : ℝ))))
              have hl : (27 / 2) * (Y : ℝ) ^ (1 - 2 * σ) * (Real.log (Y : ℝ)) ^ 2 =
                  (27 / 2) * ((Y : ℝ) ^ (1 - 2 * σ) * (Real.log (Y : ℝ)) ^ 2) := by ring
              have hr : 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 =
                  27 * ((X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2) := by ring
              linarith
      -- Interior sum: `D2 n * (w₁ n - w₁ (n+1)) ≤ 27 * (2σ + 2) * n^(-2σ) * (log(2*n))^2`
      have hterm_w1 : ∀ n ∈ Finset.Ioc X Y,
          D2 n * max 0 (w₁ n - w₁ (n + 1)) ≤
            27 * (2 * σ + 2) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 2) := by
        intro n hn
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        have hnp1_0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
        have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) :=
          hlog2.trans (Real.log_le_log (by norm_num) (Nat.cast_le.mpr hn2))
        have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
        have hlognp1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
          lt_of_lt_of_le hlogn_pos (Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.le_succ n)))
        have hdiff_le : w₁ n - w₁ (n + 1) ≤ (2 * σ + 2) / 2 * ((n : ℝ) ^ (-2 * σ - 1) / Real.log (n : ℝ)) := by
          dsimp only [w₁]; rw [if_pos hn2, if_pos (by omega : 2 ≤ n + 1)]
          have hsplit : (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ)) -
                ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) / (2 * Real.log ((n + 1 : ℕ) : ℝ)) =
              ((n : ℝ) ^ (-2 * σ) - ((n + 1 : ℕ) : ℝ) ^ (-2 * σ)) / (2 * Real.log (n : ℝ)) +
              ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) *
                (Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / (2 * Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) := by
            rw [Real.log_div hnp1_0.ne' hn0.ne']
            field_simp [hlogn_pos.ne', hlognp1_pos.ne']; ring
          rw [hsplit]
          have h1 : ((n : ℝ) ^ (-2 * σ) - ((n + 1 : ℕ) : ℝ) ^ (-2 * σ)) / (2 * Real.log (n : ℝ)) ≤
              (2 * σ) * (n : ℝ) ^ (-2 * σ - 1) / (2 * Real.log (n : ℝ)) :=
            div_le_div_of_nonneg_right (hrpow_diff n (by omega)) (by positivity)
          have hlog_ratio : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 / (n : ℝ) := by
            have h := Real.log_le_sub_one_of_pos (div_pos hnp1_0 hn0)
            have halg : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by push_cast; field_simp [hn0.ne']; ring
            linarith
          have hpow_le : ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) ≤ (n : ℝ) ^ (-2 * σ) :=
            Real.rpow_le_rpow_of_nonpos hn0 (Nat.cast_le.mpr (Nat.le_succ n)) (by linarith)
          have hpow_div : (n : ℝ) ^ (-2 * σ) * (1 / (n : ℝ)) = (n : ℝ) ^ (-2 * σ - 1) := by
            rw [mul_one_div, show (n : ℝ) ^ (-2 * σ) / (n : ℝ) = (n : ℝ) ^ (-2 * σ) / (n : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one],
              ← Real.rpow_sub hn0]
          have h2 : ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) *
                (Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / (2 * Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))) ≤
              2 * (n : ℝ) ^ (-2 * σ - 1) / (2 * Real.log (n : ℝ)) := by
            have hden : Real.log (n : ℝ) ≤ 2 * Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
              have hge : (1 / 2 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
                hlogn.trans (Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.le_succ n)))
              nlinarith
            have hlog_nn : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
              Real.log_nonneg ((one_le_div hn0).mpr (Nat.cast_le.mpr (Nat.le_succ n)))
            have hfrac : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / (2 * Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) ≤
                (1 / (n : ℝ)) / Real.log (n : ℝ) :=
              div_le_div₀ (by positivity) hlog_ratio hlogn_pos hden
            calc ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) *
                  (Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / (2 * Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)))
                ≤ (n : ℝ) ^ (-2 * σ) * ((1 / (n : ℝ)) / Real.log (n : ℝ)) :=
                  mul_le_mul hpow_le hfrac (by positivity) (Real.rpow_nonneg hn0.le _)
              _ = ((n : ℝ) ^ (-2 * σ) * (1 / (n : ℝ))) / Real.log (n : ℝ) := by ring
              _ = 2 * (n : ℝ) ^ (-2 * σ - 1) / (2 * Real.log (n : ℝ)) := by
                  rw [hpow_div]; field_simp [hlogn_pos.ne']
          have halg : 2 * σ * (n : ℝ) ^ (-2 * σ - 1) / (2 * Real.log (n : ℝ)) +
              2 * (n : ℝ) ^ (-2 * σ - 1) / (2 * Real.log (n : ℝ)) =
              (2 * σ + 2) / 2 * ((n : ℝ) ^ (-2 * σ - 1) / Real.log (n : ℝ)) := by ring
          linarith
        have hmax_le : max 0 (w₁ n - w₁ (n + 1)) ≤ (2 * σ + 2) / 2 * ((n : ℝ) ^ (-2 * σ - 1) / Real.log (n : ℝ)) :=
          max_le (by positivity) hdiff_le
        have hnpow : (n : ℝ) * (n : ℝ) ^ (-2 * σ - 1) = (n : ℝ) ^ (-2 * σ) := by
          rw [show (n : ℝ) * (n : ℝ) ^ (-2 * σ - 1) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * σ - 1) by rw [Real.rpow_one],
            ← Real.rpow_add hn0]
          congr 1; ring
        have hlog_le : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
          Real.log_le_log hn0 (by linarith)
        calc D2 n * max 0 (w₁ n - w₁ (n + 1))
            ≤ (27 * (n : ℝ) * (Real.log (n : ℝ)) ^ 3) *
                ((2 * σ + 2) / 2 * ((n : ℝ) ^ (-2 * σ - 1) / Real.log (n : ℝ))) :=
              mul_le_mul (hD2_bd n hn2) hmax_le (le_max_left _ _) (by positivity)
          _ = 27 * ((2 * σ + 2) / 2) * ((n : ℝ) * (n : ℝ) ^ (-2 * σ - 1)) * (Real.log (n : ℝ)) ^ 2 := by
              field_simp [hlogn_pos.ne']
          _ ≤ 27 * (2 * σ + 2) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 2) := by
              rw [hnpow]
              have hsq := pow_le_pow_left₀ hlogn_pos.le hlog_le 2
              have h1 := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hn0.le (-2 * σ))
              have h2 : 27 * ((2 * σ + 2) / 2) ≤ 27 * (2 * σ + 2) := by linarith
              have hmul := mul_le_mul h2 h1 (by positivity) (by linarith)
              linarith [show 27 * ((2 * σ + 2) / 2) * (n : ℝ) ^ (-2 * σ) * (Real.log (n : ℝ)) ^ 2 =
                (27 * ((2 * σ + 2) / 2)) * ((n : ℝ) ^ (-2 * σ) * (Real.log (n : ℝ)) ^ 2) by ring]
      have hint_sum : ∑ n ∈ Finset.Ioc X Y, D2 n * max 0 (w₁ n - w₁ (n + 1)) ≤
          27 * (2 * σ + 2) * C₂ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
        calc ∑ n ∈ Finset.Ioc X Y, D2 n * max 0 (w₁ n - w₁ (n + 1))
            ≤ ∑ n ∈ Finset.Ioc X Y, 27 * (2 * σ + 2) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 2) :=
              Finset.sum_le_sum hterm_w1
          _ = 27 * (2 * σ + 2) * ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 2 := by
              rw [← Finset.mul_sum]
          _ ≤ 27 * (2 * σ + 2) * (C₂ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (X : ℝ))) ^ 2) :=
              mul_le_mul_of_nonneg_left (by simpa [neg_mul] using hC₂ (Y := Y) hX) (by positivity)
          _ ≤ 27 * (2 * σ + 2) * (C₂ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2) := by
              have hlog_xy : Real.log (2 * (X : ℝ)) ≤ Real.log (2 * (Y : ℝ)) :=
                Real.log_le_log (by positivity) (by have : (X : ℝ) ≤ (Y : ℝ) := Nat.cast_le.mpr hXY; linarith)
              gcongr
          _ = 27 * (2 * σ + 2) * C₂ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 2 := by ring
      dsimp only [A₁]; linarith
  -- Bound `I₂`: `∑_{n ∈ Ioc X Y} d(n)^2 * (log n / 2) * n^(-2σ) ≤ A₂ * X^(1 - 2σ) * (log(2*Y))^4`
  have hI2_tail : ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ) ≤
      A₂ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by
    by_cases hXY' : Y ≤ X
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
    · push Not at hXY'
      have hY2 : 2 ≤ Y := by omega
      let w₂ : ℕ → ℝ := fun n => if 2 ≤ n then (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ) else 0
      have hw₂_nn : ∀ n, 0 ≤ w₂ n := fun n => by
        dsimp only [w₂]; split_ifs with h
        · have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
          positivity
        · exact le_rfl
      have hrew : ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ) =
          ∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * w₂ n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        dsimp only [w₂]; rw [if_pos hn2]; ring
      rw [hrew]
      refine (habel w₂ hw₂_nn).trans ?_
      have hbd_Y : D2 Y * w₂ Y ≤ 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by
        dsimp only [w₂]; rw [if_pos hY2]
        have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
        have hlogY_le : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
          Real.log_le_log hY0 (by linarith)
        have hDY := hD2_bd Y hY2
        have hYpow : (Y : ℝ) * (Y : ℝ) ^ (-2 * σ) = (Y : ℝ) ^ (1 - 2 * σ) := by
          rw [show (Y : ℝ) * (Y : ℝ) ^ (-2 * σ) = (Y : ℝ) ^ (1 : ℝ) * (Y : ℝ) ^ (-2 * σ) by rw [Real.rpow_one],
            ← Real.rpow_add hY0]
          congr 1; ring
        have hYX : (Y : ℝ) ^ (1 - 2 * σ) ≤ (X : ℝ) ^ (1 - 2 * σ) :=
          Real.rpow_le_rpow_of_nonpos hX0 (Nat.cast_le.mpr hXY) (by linarith)
        calc D2 Y * ((Real.log (Y : ℝ) / 2) * (Y : ℝ) ^ (-2 * σ))
            ≤ (27 * (Y : ℝ) * (Real.log (Y : ℝ)) ^ 3) * ((Real.log (Y : ℝ) / 2) * (Y : ℝ) ^ (-2 * σ)) :=
              mul_le_mul_of_nonneg_right hDY (by positivity)
          _ = (27 / 2) * ((Y : ℝ) * (Y : ℝ) ^ (-2 * σ)) * (Real.log (Y : ℝ)) ^ 4 := by ring
          _ ≤ 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by
              rw [hYpow]
              have h4 := pow_le_pow_left₀ hlogY.le hlogY_le 4
              have h1 := mul_le_mul hYX h4 (pow_nonneg hlogY.le 4) (Real.rpow_nonneg hX0.le _)
              have hnn := mul_nonneg (Real.rpow_nonneg hX0.le (1 - 2 * σ)) (pow_nonneg (by linarith : 0 ≤ Real.log (2 * (Y : ℝ))) 4)
              have hl : (27 / 2) * (Y : ℝ) ^ (1 - 2 * σ) * (Real.log (Y : ℝ)) ^ 4 =
                  (27 / 2) * ((Y : ℝ) ^ (1 - 2 * σ) * (Real.log (Y : ℝ)) ^ 4) := by ring
              have hr : 27 * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 =
                  27 * ((X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4) := by ring
              linarith
      have hterm_w2 : ∀ n ∈ Finset.Ioc X Y,
          D2 n * max 0 (w₂ n - w₂ (n + 1)) ≤
            27 * (2 * σ) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 4) := by
        intro n hn
        have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
          Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.le_succ n))
        have hdiff_le : w₂ n - w₂ (n + 1) ≤ (2 * σ) * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ - 1) := by
          dsimp only [w₂]; rw [if_pos hn2, if_pos (by omega : 2 ≤ n + 1)]
          have h1 : (Real.log (n : ℝ) / 2) * ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) ≤
              (Real.log ((n + 1 : ℕ) : ℝ) / 2) * ((n + 1 : ℕ) : ℝ) ^ (-2 * σ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          have h2 : (Real.log (n : ℝ) / 2) * ((n : ℝ) ^ (-2 * σ) - ((n + 1 : ℕ) : ℝ) ^ (-2 * σ)) ≤
              (Real.log (n : ℝ) / 2) * (2 * σ * (n : ℝ) ^ (-2 * σ - 1)) :=
            mul_le_mul_of_nonneg_left (hrpow_diff n (by omega)) (by positivity)
          linarith
        have hmax_le : max 0 (w₂ n - w₂ (n + 1)) ≤ (2 * σ) * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ - 1) :=
          max_le (by positivity) hdiff_le
        have hnpow : (n : ℝ) * (n : ℝ) ^ (-2 * σ - 1) = (n : ℝ) ^ (-2 * σ) := by
          rw [show (n : ℝ) * (n : ℝ) ^ (-2 * σ - 1) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * σ - 1) by rw [Real.rpow_one],
            ← Real.rpow_add hn0]
          congr 1; ring
        have hlog_le : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
          Real.log_le_log hn0 (by linarith)
        calc D2 n * max 0 (w₂ n - w₂ (n + 1))
            ≤ (27 * (n : ℝ) * (Real.log (n : ℝ)) ^ 3) *
                ((2 * σ) * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ - 1)) :=
              mul_le_mul (hD2_bd n hn2) hmax_le (le_max_left _ _) (by positivity)
          _ = (27 / 2) * (2 * σ) * ((n : ℝ) * (n : ℝ) ^ (-2 * σ - 1)) * (Real.log (n : ℝ)) ^ 4 := by ring
          _ ≤ 27 * (2 * σ) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 4) := by
              rw [hnpow]
              have h4 := pow_le_pow_left₀ hlogn_pos.le hlog_le 4
              have h1 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hn0.le (-2 * σ))
              have h2 : (27 / 2) * (2 * σ) ≤ 27 * (2 * σ) := by linarith
              have hmul := mul_le_mul h2 h1 (by positivity) (by linarith)
              linarith [show (27 / 2) * (2 * σ) * (n : ℝ) ^ (-2 * σ) * (Real.log (n : ℝ)) ^ 4 =
                ((27 / 2) * (2 * σ)) * ((n : ℝ) ^ (-2 * σ) * (Real.log (n : ℝ)) ^ 4) by ring]
      have hint_sum : ∑ n ∈ Finset.Ioc X Y, D2 n * max 0 (w₂ n - w₂ (n + 1)) ≤
          27 * (2 * σ) * C₄ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by
        calc ∑ n ∈ Finset.Ioc X Y, D2 n * max 0 (w₂ n - w₂ (n + 1))
            ≤ ∑ n ∈ Finset.Ioc X Y, 27 * (2 * σ) * ((n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 4) :=
              Finset.sum_le_sum hterm_w2
          _ = 27 * (2 * σ) * ∑ n ∈ Finset.Ioc X Y, (n : ℝ) ^ (-2 * σ) * (Real.log (2 * (n : ℝ))) ^ 4 := by
              rw [← Finset.mul_sum]
          _ ≤ 27 * (2 * σ) * (C₄ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (X : ℝ))) ^ 4) :=
              mul_le_mul_of_nonneg_left (by simpa [neg_mul] using hC₄ (Y := Y) hX) (by positivity)
          _ ≤ 27 * (2 * σ) * (C₄ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4) := by
              have hlog_xy : Real.log (2 * (X : ℝ)) ≤ Real.log (2 * (Y : ℝ)) :=
                Real.log_le_log (by positivity) (by have : (X : ℝ) ≤ (Y : ℝ) := Nat.cast_le.mpr hXY; linarith)
              gcongr
          _ = 27 * (2 * σ) * C₄ * (X : ℝ) ^ (1 - 2 * σ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by ring
      dsimp only [A₂]; linarith
  -- Step 6: Combine lower bound `(1/4) * S.card ≤ ∑_{ρ ∈ S} ‖F ρ‖^2` with `hsum_F_bd`, `hI1_tail`, `hI2_tail`!
  have hlower : (1 / 4 : ℝ) * (S.card : ℝ) ≤ ∑ ρ ∈ S, ‖F ρ‖ ^ 2 := by
    calc (1 / 4 : ℝ) * (S.card : ℝ)
        = ∑ _ ∈ S, (1 / 4 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ ρ ∈ S, ‖F ρ‖ ^ 2 := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have h := hdet ρ hρ
          have hsq := pow_le_pow_left₀ (by norm_num) h 2
          linarith [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
  have hcomb_tail :
      α₀ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ))) +
      α₀⁻¹ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ)) ≤
      (A₁ + A₂) * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3 := by
    have h1 : α₀ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) / (2 * Real.log (n : ℝ))) ≤
        A₁ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hI1_tail hα₀_pos.le
      linarith [show α₀ * (A₁ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 2) = A₁ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3 by ring]
    have h2 : α₀⁻¹ * (∑ n ∈ Finset.Ioc X Y, (n.divisors.card : ℝ) ^ 2 * (Real.log (n : ℝ) / 2) * (n : ℝ) ^ (-2 * σ)) ≤
        A₂ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hI2_tail (inv_nonneg.mpr hα₀_pos.le)
      have halg : α₀⁻¹ * (A₂ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 4) = A₂ * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3 := by
        field_simp [hα₀_pos.ne']
      linarith
    linarith
  have hupper : ∑ ρ ∈ S, ‖F ρ‖ ^ 2 ≤
      K₀ * (A₁ + A₂) * (T + (Y : ℝ)) * α₀ ^ 4 * (X : ℝ) ^ (1 - 2 * σ) := by
    have hmul := mul_le_mul_of_nonneg_left hcomb_tail
      (by positivity : 0 ≤ K₀ * (T + (Y : ℝ)) * α₀)
    have h1 := hsum_F_bd.trans hmul
    linarith [show K₀ * (T + (Y : ℝ)) * α₀ * ((A₁ + A₂) * (X : ℝ) ^ (1 - 2 * σ) * α₀ ^ 3) =
      K₀ * (A₁ + A₂) * (T + (Y : ℝ)) * α₀ ^ 4 * (X : ℝ) ^ (1 - 2 * σ) by ring]
  linarith

end RHDirect.Stage10ZeroDensity
