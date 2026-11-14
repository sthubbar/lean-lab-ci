import LeanLab.ExceptionalSet.Counting385
import LeanLab.ExceptionalSet.PintzAlthofer2026Sup
import LeanLab.ExceptionalSet.Supply480

/-!
P0029 pages 10 to 13, displays 3.5 to 3.8.
Split the analytic approximation from the singular series reconstruction.
The rectangular arc model is the existing Vfun at order floor sqrt X.
Its arcs can overlap. No assertion that they are a Farey partition is used.
The two estimates below include the cost of this reconstruction.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF. P0029 page 12 display 3.7 and page 13 display 3.8.
The full arc approximation in mean square, not merely the centre estimate.
The finite exponential sum is cut at X squared, leaving coefficients up to X exact.
The rectangular model includes the Farey boundary reconstruction cost. -/
theorem leaf_arc_energy (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Removing the exponential smoothing costs at most exp two on a prefix.
Source: P0029 page 10 display 3.2 with R equal to exp minus one over X. -/
theorem unsmooth_square {X n : ℕ} (hX : 1 ≤ X) (hn : n ≤ X) (a : ℝ) :
    a ^ 2 ≤ Real.exp 2 * (Real.exp (-(n : ℝ) / X) * a) ^ 2 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hr : (n : ℝ) / X ≤ 1 := (div_le_one hX0).mpr (by exact_mod_cast hn)
  have he : 1 ≤ Real.exp (2 - 2 * (n : ℝ) / X) :=
    Real.one_le_exp (by rw [mul_div_assoc]; linarith)
  have hid : Real.exp 2 * (Real.exp (-(n : ℝ) / X) * a) ^ 2 =
      Real.exp (2 - 2 * (n : ℝ) / X) * a ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hid]
  exact le_mul_of_one_le_left (sq_nonneg a) he

/-- Bessel controls the even coefficient error of the generating function model.
Source: P0029 page 13 display 3.8, the Parseval step. -/
theorem even_bessel (X : ℕ) (W : AddCircle (1 : ℝ) → ℂ) (hW : MemLp W 2 haarAddCircle) :
    ∑ n ∈ (range (X + 1)).filter Even,
      ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) - fourierCoeff W (n : ℤ)‖ ^ 2 ≤
        ∫ t, ‖FX X (X ^ 2) t ^ 2 - W t‖ ^ 2 ∂haarAddCircle := by
  let G : AddCircle (1 : ℝ) → ℂ := fun t => FX X (X ^ 2) t ^ 2 - W t
  have hF := memLp_FX_sq (X : ℝ) (X ^ 2)
  have hG : MemLp G 2 haarAddCircle := hF.sub hW
  have hcoef (n : ℕ) (hn : n ≤ X) : fourierCoeff G (n : ℤ) =
      ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) - fourierCoeff W (n : ℤ) := by
    have hadd := fourierCoeff.add (T := (1 : ℝ))
      (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
      (hF.integrable one_le_two) (hW.integrable one_le_two).neg
    have hneg : fourierCoeff (-W) = -fourierCoeff W := by
      ext m
      have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
      simpa [neg_smul, one_smul] using h
    have heq : G = (fun t => FX X (X ^ 2) t ^ 2) + -W := by
      ext t
      simp [G, sub_eq_add_neg]
    rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply,
      fourierCoeff_FX_sq (X : ℝ) (X ^ 2) n (hn.trans (Nat.le_self_pow two_ne_zero X))]
    rfl
  have hb := bessel_finset hG (((range (X + 1)).filter Even).image (fun n : ℕ => (n : ℤ)))
  rw [sum_image (fun a _ b _ h => by exact_mod_cast h)] at hb
  convert hb using 1
  apply sum_congr rfl
  intro n hn
  rw [hcoef n (by have := mem_range.mp (mem_filter.mp hn).1; omega)]

/-- The finite error energy follows from the two distinct model errors.
Source: P0029 page 13 display 3.8. CONDITIONAL ON the two explicit energy bounds. -/
theorem energy_of_model (X : ℕ) (hX : 1 ≤ X) (W : AddCircle (1 : ℝ) → ℂ)
    (hW : MemLp W 2 haarAddCircle) (A B : ℝ)
    (hA : (∫ t, ‖FX X (X ^ 2) t ^ 2 - W t‖ ^ 2 ∂haarAddCircle) ≤ A)
    (hB : (∑ n ∈ (range (X + 1)).filter Even,
      ‖fourierCoeff W (n : ℤ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) ≤ B) :
    ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
      2 * Real.exp 2 * (A + B) := by
  let s := (range (X + 1)).filter Even
  let u := fun n => ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) - fourierCoeff W (n : ℤ)
  let v : ℕ → ℂ := fun n => fourierCoeff W (n : ℤ) -
    ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)
  have hp (n : ℕ) (hn : n ∈ s) : (error n) ^ 2 ≤
      2 * Real.exp 2 * (‖u n‖ ^ 2 + ‖v n‖ ^ 2) := by
    have hnX : n ≤ X := by have := mem_range.mp (mem_filter.mp hn).1; omega
    have hid : u n + v n = ((Real.exp (-(n : ℝ) / X) * error n : ℝ) : ℂ) := by
      dsimp [u, v, error]
      push_cast
      ring
    have hnorm : ‖u n + v n‖ ^ 2 ≤ 2 * (‖u n‖ ^ 2 + ‖v n‖ ^ 2) :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
    rw [hid, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hnorm
    exact (unsmooth_square hX hnX (error n)).trans (by
      nlinarith [Real.exp_pos (2 : ℝ)])
  calc ∑ n ∈ s, (error n) ^ 2
      ≤ ∑ n ∈ s, 2 * Real.exp 2 * (‖u n‖ ^ 2 + ‖v n‖ ^ 2) := sum_le_sum hp
    _ = 2 * Real.exp 2 * ((∑ n ∈ s, ‖u n‖ ^ 2) + ∑ n ∈ s, ‖v n‖ ^ 2) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ 2 * Real.exp 2 * (A + B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add ((even_bessel X W hW).trans hA) hB


open Finset Real
open LeanLab.Routes.R5060
open LeanLab.ExceptionalSet.PintzAlthofer2026Coef
open LeanLab.ExceptionalSet.PintzAlthofer2026Tail

/-- Absolute convergence of the binary Ramanujan series.
Source: P0029 page 12, the singular series display after 3.7. -/
theorem singular_terms_summable (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => ‖bS n q‖) := by
  apply summable_of_sum_le (fun q => norm_nonneg _)
    (c := 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt (1 / 2))
  intro s
  have hsum : ∑ q ∈ s, ‖bS n q‖ = ∑ q ∈ s.filter (0 < ·), ‖bS n q‖ := by
    symm
    apply sum_subset (filter_subset _ _)
    intro q hq hnot
    have hq0 : q = 0 := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hq, Nat.pos_of_ne_zero h⟩)
    simp [hq0]
  rw [hsum]
  calc ∑ q ∈ s.filter (0 < ·), ‖bS n q‖
      ≤ ∑ q ∈ s.filter (0 < ·),
        |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 := by
          apply sum_le_sum
          intro q hq
          simpa only [Real.norm_eq_abs] using abs_bS_le n q (mem_filter.mp hq).2
    _ ≤ _ := tail_sum n hn (by norm_num : (0:ℝ) < 1/2) _ (by
      intro q hq
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (mem_filter.mp hq).2
      linarith)

/-- Uniform absolute tail of the binary Ramanujan series.
Source: P0029 page 12, the singular series display after 3.7. -/
theorem singular_terms_tail (n : ℕ) (hn : 1 ≤ n) (P : ℝ) (hP : 0 < P) :
    (∑' q : ℕ, if P < q then ‖bS n q‖ else 0) ≤
      12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P := by
  apply Real.tsum_le_of_sum_le (fun q => by positivity)
  intro s
  rw [← sum_filter]
  calc ∑ q ∈ s.filter (fun q : ℕ => P < q), ‖bS n q‖
      ≤ ∑ q ∈ s.filter (fun q : ℕ => P < q),
        |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 := by
          apply sum_le_sum
          intro q hq
          have hq0 : (0:ℝ) < q := hP.trans (mem_filter.mp hq).2
          simpa only [Real.norm_eq_abs] using abs_bS_le n q (by exact_mod_cast hq0)
    _ ≤ _ := tail_sum n hn hP _ (fun q hq => (mem_filter.mp hq).2)

/-- Euler factors have only the zeroth and first prime powers.
Source: P0029 page 12, the singular series display after 3.7. -/
theorem singular_prime_power_sum (n p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, bS n (p ^ k)) = 1 + bS n p := by
  classical
  rw [tsum_eq_sum (s := {0, 1})]
  · simp only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true, sum_singleton, pow_zero, pow_one]
    rw [(bS_mult n).map_one]
  · intro k hk
    have hk0 : k ≠ 0 := by intro h; exact hk (by simp [h])
    have hk1 : k ≠ 1 := by intro h; exact hk (by simp [h])
    apply bS_eq_zero (one_le_pow₀ hp.one_lt.le)
    rw [Nat.squarefree_pow_iff hp.ne_one hk0]
    exact fun h => hk1 h.2

/-- The absolutely convergent binary Ramanujan series equals its prime Euler product.
Source: P0029 page 12, the singular series display after 3.7. -/
theorem singular_euler_product (n : ℕ) (hn : 1 ≤ n) :
    (∏' p : Nat.Primes, (1 + bS n p)) = ∑' q : ℕ, bS n q := by
  have h := (bS_mult n).eulerProduct_tprod (singular_terms_summable n hn)
  calc
    _ = ∏' p : Nat.Primes, ∑' k : ℕ, bS n ((p : ℕ) ^ k) := by
      apply tprod_congr
      intro p
      exact (singular_prime_power_sum n p p.property).symm
    _ = _ := h


/-- Identification of the convergent Ramanujan series with the even Euler product.
Source: P0029 page 6 display 2.10 and page 12 after display 3.7. -/
theorem singular_series_eq (n : ℕ) (hn : 1 ≤ n) (heven : Even n) :
    (∑' q : ℕ, bS n q) = Sing n := by
  classical
  let s := n.primeFactors.filter (2 < ·)
  let F : ℕ → ℝ := fun p => if p.Prime then 1 + bS n p else 1
  let f : ℕ → ℝ := fun p => if p = 2 then 2 else 1
  let g : ℕ → ℝ := fun p => if p.Prime ∧ 2 < p then 1 - 1 / ((p:ℝ)-1)^2 else 1
  let k : ℕ → ℝ := fun p => if p ∈ s then 1 + 1 / ((p:ℝ)-2) else 1
  have hf : Multipliable f := multipliable_of_ne_finset_one (s := {2}) (by simp [f])
  have hk : Multipliable k := multipliable_of_ne_finset_one (s := s) (by intro p hp; simp only [k, ite_eq_right hp])
  have hg : Multipliable g := by
    have h := Real.multipliable_one_add_of_summable summable_inv_sq_sub_one
    have h' : Multipliable (fun p : {p:ℕ // p.Prime ∧ 2 < p} =>
        1 - 1 / ((p.1:ℝ)-1)^2) := by simpa only [sub_eq_add_neg] using h
    have h'' := (multipliable_subtype_iff_mulIndicator
      (f := fun p : ℕ => 1 - 1 / ((p:ℝ)-1)^2)
      (s := {p : ℕ | p.Prime ∧ 2 < p})).mp h'
    have heq : g = {p : ℕ | p.Prime ∧ 2 < p}.mulIndicator
        (fun p : ℕ => 1 - 1 / ((p:ℝ)-1)^2) := by
      funext p
      by_cases hp : p.Prime ∧ 2 < p <;> simp [g, Set.mulIndicator, hp]
    rw [heq]
    exact h''
  have hF (p : ℕ) : F p = f p * g p * k p := by
    by_cases hp : p.Prime
    · by_cases hp2 : p = 2
      · subst p
        simp [F, f, g, k, s, one_add_bS_two heven, Nat.prime_two]
      · have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
        have hpr : (2:ℝ) < p := by exact_mod_cast hpgt
        have hmem : p ∈ s ↔ p ∣ n := by
          simp [s, Nat.mem_primeFactors, hp, hpgt, show n ≠ 0 by omega]
        simp only [F, ite_eq_left hp, f, ite_eq_right hp2, g,
          ite_eq_left (show p.Prime ∧ 2 < p from ⟨hp, hpgt⟩), one_mul,
          k, hmem, one_add_bS_prime hp]
        have h1 : (p:ℝ)-1 ≠ 0 := by linarith
        have h2 : (p:ℝ)-2 ≠ 0 := by linarith
        split_ifs <;> field_simp [h1, h2] <;> ring
    · have hnot : p ∉ s := by
        intro h
        exact hp (Nat.prime_of_mem_primeFactors (mem_filter.mp h).1)
      simp [F, f, g, k, hp, hnot, show p ≠ 2 by intro h; exact hp (h ▸ Nat.prime_two)]
  have hsub (P : ℕ → Prop) (a : ℕ → ℝ) :
      (∏' p : {p : ℕ // P p}, a p.1) = ∏' p : ℕ, if P p then a p else 1 := by
    let e : {p : ℕ // P p} ≃ ↑{p : ℕ | P p} :=
      { toFun := fun p => ⟨p.1, by simpa only [Set.mem_ofPred_eq] using p.2⟩
        invFun := fun p => ⟨p.1, by simpa only [Set.mem_ofPred_eq] using p.2⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
    calc
      _ = ∏' p : {p : ℕ // P p}, a (e p).1 := by
        apply tprod_congr
        intro p
        rfl
      _ = ∏' p : ↑{p : ℕ | P p}, a p.1 := e.tprod_eq (fun p => a p.1)
      _ = _ := by
        simpa only [Set.mulIndicator, Set.mem_ofPred_eq] using
          (_root_.tprod_subtype {p : ℕ | P p} a)
  have hprodF : (∏' p : ℕ, F p) = ∑' q : ℕ, bS n q := by
    rw [← singular_euler_product n hn]
    symm
    convert hsub Nat.Prime (fun p => 1 + bS n p) using 1
    · apply tprod_congr
      intro p
      rfl
    · apply tprod_congr
      intro p
      by_cases hp : p.Prime <;> simp [F, hp]
  have hprodg : (∏' p : ℕ, g p) = C0 := by
    symm
    convert hsub (fun p => p.Prime ∧ 2 < p) (fun p => 1 - 1 / ((p:ℝ)-1)^2) using 1
    · apply tprod_congr
      intro p
      rfl
    · apply tprod_congr
      intro p
      by_cases hp : p.Prime ∧ 2 < p <;> simp [g, hp]
  have hprodf : (∏' p : ℕ, f p) = 2 := by
    rw [tprod_eq_prod (s := {2}) (by simp [f])]
    simp [f]
  have hprodk : (∏' p : ℕ, k p) = ∏ p ∈ s, (1 + 1 / ((p:ℝ)-2)) := by
    rw [tprod_eq_prod (s := s) (by intro p hp; simp only [k, ite_eq_right hp])]
    apply prod_congr rfl
    intro p hp
    simp [k, hp]
  rw [← hprodF]
  simp_rw [hF]
  rw [(hf.mul hg).tprod_mul hk, hf.tprod_mul hg, hprodf, hprodg, hprodk]
  rfl


/-- Quantitative reconstruction of the even singular series by its initial moduli.
Source: P0029 page 6 displays 2.9 and 2.10 and page 12 after display 3.7. -/
theorem singular_partial_error (n P : ℕ) (hn : 1 ≤ n) (heven : Even n) (hP : 1 ≤ P) :
    ‖(∑ q ∈ Icc 1 P, bS n q) - Sing n‖ ≤
      12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P := by
  have hPr : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hnorm : Summable (fun i : ℕ => ‖bS n (i + (P + 1))‖) :=
    (singular_terms_summable n hn).comp_injective (by intro i j h; dsimp at h; omega)
  have ht : (∑' i : ℕ, ‖bS n (i + (P + 1))‖) ≤
      12 * (n.divisors.card : ℝ)^2 / Real.sqrt P := by
    apply Real.tsum_le_of_sum_le (fun i => norm_nonneg _)
    intro S
    have hsum : (∑ q ∈ S.image (fun i => i + (P + 1)), ‖bS n q‖) =
        ∑ i ∈ S, ‖bS n (i + (P + 1))‖ :=
      sum_image (by intro i hi j hj h; dsimp at h; omega)
    rw [← hsum]
    calc ∑ q ∈ S.image (fun i => i + (P + 1)), ‖bS n q‖
        ≤ ∑ q ∈ S.image (fun i => i + (P + 1)),
          |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q:ℝ)^2 := by
            apply sum_le_sum
            intro q hq
            rcases mem_image.mp hq with ⟨i, hi, rfl⟩
            simpa only [Real.norm_eq_abs] using abs_bS_le n (i+(P+1)) (by omega)
      _ ≤ _ := tail_sum n hn hPr _ (by
        intro q hq
        rcases mem_image.mp hq with ⟨i, hi, rfl⟩
        exact_mod_cast (show P < i + (P + 1) by omega))
  have hs := (singular_terms_summable n hn).of_norm.sum_add_tsum_nat_add (P + 1)
  have hrange : range (P+1) = insert 0 (Icc 1 P) := by
    ext q
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add] at hs
  have heq : (∑ q ∈ Icc 1 P, bS n q) - Sing n =
      -(∑' i : ℕ, bS n (i + (P + 1))) := by
    rw [← singular_series_eq n hn heven, ← hs]
    ring
  rw [heq, norm_neg]
  exact (norm_tsum_le_tsum_norm hnorm).trans ht

/-- Explicit model coefficient error, with beta truncation and arithmetic tail separated.
Source: P0029 page 12 main term displays after 3.7 and page 13 display 3.8. -/
theorem model_coefficient_error (n P : ℕ) (X : ℝ) (hn : 1 ≤ n) (heven : Even n)
    (hP : 1 ≤ P) (hX : 0 < X) (h2P : 2 * (P : ℝ) ≤ X) :
    ‖fourierCoeff (LeanLab.ExceptionalSet.PintzAlthofer2026Model.Vfun X P P) (n : ℤ) -
      ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ≤
      (∑ q ∈ Icc 1 P, |bS n q| * ((q : ℝ) * X / (2 * Real.pi ^ 2 * P))) +
      ((n : ℝ) * Real.exp (-(n : ℝ) / X)) *
        (12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let w : ℕ → ℂ := fun q => ((bS n q : ℝ) : ℂ)
  let A : ℝ := (n : ℝ) * Real.exp (-(n : ℝ) / X)
  have hA : 0 ≤ A := by positivity
  have hw : (∑ q ∈ Icc 1 P, w q) = ((∑ q ∈ Icc 1 P, bS n q : ℝ) : ℂ) := by
    simp [w]
  have htail : ‖(A : ℂ) * (∑ q ∈ Icc 1 P, w q) -
      ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ≤
      A * (12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) := by
    have hid : (A : ℂ) * (∑ q ∈ Icc 1 P, w q) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) =
        ((A * ((∑ q ∈ Icc 1 P, bS n q) - Sing n) : ℝ) : ℂ) := by
      rw [hw]
      dsimp [A]
      push_cast
      ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left (singular_partial_error n P hn heven hP) hA
  rw [LeanLab.ExceptionalSet.PintzAlthofer2026Model.fourierCoeff_Vfun hX hPr.le h2P]
  have hb := LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc_approx hX hPr hnr P w
  have hnorm : (∑ q ∈ Icc 1 P, ‖w q‖ * ((q : ℝ) * X / (2 * Real.pi ^ 2 * P))) =
      ∑ q ∈ Icc 1 P, |bS n q| * ((q : ℝ) * X / (2 * Real.pi ^ 2 * P)) := by
    simp [w, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hb
  calc
    _ ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P P w n -
        (A : ℂ) * ∑ q ∈ Icc 1 P, w q‖ +
      ‖(A : ℂ) * (∑ q ∈ Icc 1 P, w q) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc X P P w n)
            ((A : ℂ) * ∑ q ∈ Icc 1 P, w q)
            (((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ))
    _ ≤ _ := add_le_add hb htail


/-- Uniform divisor factor absorption for the model coefficient residual.
Source: P0029 page 12 after display 3.7, derived epsilon loss. -/
theorem divisor_square_power (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ n X : ℕ, 1 ≤ n → n ≤ X →
      (n.divisors.card : ℝ) ^ 2 ≤ D * (X : ℝ) ^ η := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hη)
  obtain ⟨D, hD, hd⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow (k + 1) (by omega)
  refine ⟨D ^ 2, sq_pos_of_pos hD, ?_⟩
  intro n X hn hnX
  have hX : (1 : ℝ) ≤ X := by exact_mod_cast (hn.trans hnX)
  have hm : (n : ℝ) ^ (((k+1 : ℕ):ℝ)⁻¹) ≤ (X : ℝ) ^ (((k+1 : ℕ):ℝ)⁻¹) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnX) (by positivity)
  have he : (((k+1 : ℕ):ℝ)⁻¹) * 2 ≤ η := by
    push_cast
    rw [one_div] at hk
    linarith
  calc (n.divisors.card : ℝ)^2 ≤ (D * (X:ℝ)^(((k+1:ℕ):ℝ)⁻¹))^2 :=
      pow_le_pow_left₀ (by positivity) ((hd n hn).trans (mul_le_mul_of_nonneg_left hm hD.le)) 2
    _ = D^2 * (X:ℝ)^((((k+1:ℕ):ℝ)⁻¹)*2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
      norm_num
    _ ≤ D^2 * (X:ℝ)^η :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX he) (sq_nonneg _)

/-- Uniform logarithm factor absorption for the model coefficient residual.
Source: P0029 page 12 after display 3.7, derived epsilon loss. -/
theorem log_square_power (η : ℝ) (hη : 0 < η) {X : ℝ} (hX : 1 ≤ X) :
    (1 + Real.log X)^2 ≤ (1 + 2 / η)^2 * X^η := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hp : 1 ≤ X^(η/2) := Real.one_le_rpow hX (by positivity)
  have hl := Real.log_le_rpow_div hX0.le (show 0 < η/2 by positivity)
  have hsum : 1 + Real.log X ≤ (1 + 2/η) * X^(η/2) := by
    have heq : X^(η/2) / (η/2) = (2/η) * X^(η/2) := by field_simp
    rw [heq] at hl
    nlinarith
  calc (1 + Real.log X)^2 ≤ ((1 + 2/η) * X^(η/2))^2 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) hsum 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hX0.le]
      congr 2
      norm_num

/-- Elementary bounds for the Farey order equal to floor square root X.
Source: P0029 page 10 after display 3.2. -/
theorem sqrt_cutoff_bounds (X : ℕ) (hX : 4 ≤ X) :
    2 ≤ Nat.sqrt X ∧ Nat.sqrt X ≤ X ∧ 2 * Nat.sqrt X ≤ X ∧
      (X : ℝ) ≤ 4 * (Nat.sqrt X : ℝ)^2 := by
  have hp : 2 ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by norm_num; exact hX)
  have hlo := Nat.sqrt_le' X
  have hup := Nat.lt_succ_sqrt' X
  have hlin : 2 * Nat.sqrt X ≤ X := by
    nlinarith [Nat.mul_le_mul_left (Nat.sqrt X) hp]
  have hfour : X ≤ 4 * (Nat.sqrt X)^2 := by
    nlinarith [Nat.le_self_pow two_ne_zero (Nat.sqrt X)]
  exact ⟨hp, Nat.sqrt_le_self X, hlin, by exact_mod_cast hfour⟩

/-- Division by the Farey cutoff and its square root costs at most X to three quarters.
Source: P0029 pages 10 to 12, derived square root cutoff estimates. -/
theorem sqrt_cutoff_quotients (X : ℕ) (hX : 4 ≤ X) :
    (X : ℝ) / Nat.sqrt X ≤ 2 * (X : ℝ)^(3/4:ℝ) ∧
      (X : ℝ) / Real.sqrt (Nat.sqrt X) ≤ 2 * (X : ℝ)^(3/4:ℝ) := by
  obtain ⟨hp, hpX, h2p, hfour⟩ := sqrt_cutoff_bounds X hX
  have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hp0 : (0:ℝ) < Nat.sqrt X := by exact_mod_cast (show 0 < Nat.sqrt X by omega)
  have hroot : Real.sqrt X ≤ 2 * (Nat.sqrt X : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hquart : (X:ℝ)^(1/4:ℝ) ≤ 2 * Real.sqrt (Nat.sqrt X) := by
    have hrootroot : Real.sqrt (Real.sqrt X) ≤ 2 * Real.sqrt (Nat.sqrt X) :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by
        nlinarith [Real.sq_sqrt hp0.le]⟩
    have hid : Real.sqrt (Real.sqrt (X:ℝ)) = (X:ℝ)^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
      norm_num
    rwa [hid] at hrootroot
  constructor
  · have hx : (X:ℝ) ≤ (2 * Real.sqrt X) * Nat.sqrt X := by
      nlinarith [Real.sq_sqrt hX0.le,
        mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (X:ℝ))]
    calc (X:ℝ) / Nat.sqrt X ≤ 2 * Real.sqrt X := (div_le_iff₀ hp0).mpr hx
      _ ≤ _ := by
        rw [Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by norm_num)
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
    calc (X:ℝ) = (X:ℝ)^(3/4:ℝ) * (X:ℝ)^(1/4:ℝ) := by
          rw [← Real.rpow_add hX0]
          norm_num
      _ ≤ (X:ℝ)^(3/4:ℝ) * (2 * Real.sqrt (Nat.sqrt X)) :=
          mul_le_mul_of_nonneg_left hquart (by positivity)
      _ = _ := by ring

/-- Positive even model coefficients have the required uniform power error.
Source: P0029 page 12 after display 3.7 and page 13 display 3.8. -/
theorem model_coefficient_growth (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X n : ℕ, 4 ≤ X → 1 ≤ n → Even n → n ≤ X →
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
        ((Real.exp (-(n:ℝ)/X) * (n:ℝ) * Sing n : ℝ) : ℂ)‖ ≤
        K * (X:ℝ)^(3/4 + η) := by
  obtain ⟨C, hC, h415⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026Sum415.sum415
  obtain ⟨D, hD, hd⟩ := divisor_square_power (η/2) (by positivity)
  let L : ℝ := 1 + 1 / Real.log 2
  let G : ℝ := (1 + 2 / (η/2))^2
  let H : ℝ := 2*C*Real.exp 1*L + 24
  have hL : 0 < L := by dsimp [L]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H*D*G, by positivity, ?_⟩
  intro X n hX hn heven hnX
  let P := Nat.sqrt X
  obtain ⟨hp, hpX, h2p, hfour⟩ := sqrt_cutoff_bounds X hX
  have hp1 : 1 ≤ P := by dsimp [P]; omega
  have hp0 : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hlogX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hX1
  have hlogP : 0 ≤ Real.log (P:ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlPX : Real.log (P:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpX)
  let T : ℝ := (n.divisors.card:ℝ)^2
  let M : ℝ := (1+Real.log (X:ℝ))^2
  let R : ℝ := (X:ℝ)^(3/4:ℝ)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (Real.log (X:ℝ))]
  have hlogs : (1+Real.log (P:ℝ)/Real.log 2)*(1+Real.log (P:ℝ)) ≤ L*M := by
    have hl : 1+Real.log (P:ℝ)/Real.log 2 ≤ L*(1+Real.log (X:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right hlPX (inv_nonneg.mpr hlog2.le)
      dsimp [L]
      simp only [div_eq_mul_inv, one_mul]
      nlinarith [inv_nonneg.mpr hlog2.le]
    calc _ ≤ (L*(1+Real.log (X:ℝ)))*(1+Real.log (X:ℝ)) :=
        mul_le_mul hl (by linarith) (by linarith) (by positivity)
      _ = _ := by dsimp [M]; ring
  have hsum : (∑ q ∈ Icc 1 P, (q:ℝ)*|bS n q|) ≤ C*Real.exp 1*L*T*M := by
    calc _ ≤ ∑ q ∈ Icc 1 P,
          (q:ℝ)*|LeanLab.HeathBrown1985.ramanujan q n| /(Nat.totient q:ℝ)^2 := by
            apply sum_le_sum
            intro q hq
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (abs_bS_le n q (mem_Icc.mp hq).1) (Nat.cast_nonneg _)
      _ ≤ C*(Real.exp 1*(1+Real.log P/Real.log 2))*T*(1+Real.log P) := h415 n P hn
      _ = (C*Real.exp 1*T)*((1+Real.log P/Real.log 2)*(1+Real.log P)) := by ring
      _ ≤ (C*Real.exp 1*T)*(L*M) := mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = _ := by ring
  obtain ⟨hquot, hsquot⟩ := sqrt_cutoff_quotients X hX
  have hden : (X:ℝ)/(2*Real.pi^2*P) ≤ 2*R := by
    have hpi : (1:ℝ) ≤ 2*Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have hpden : (P:ℝ) ≤ 2*Real.pi^2*P := by
      simpa using mul_le_mul_of_nonneg_right hpi hp0.le
    exact (div_le_div_of_nonneg_left hX0.le hp0 hpden).trans hquot
  have hbeta : (∑ q ∈ Icc 1 P, |bS n q| *((q:ℝ)*X/(2*Real.pi^2*P))) ≤
      (2*R)*(C*Real.exp 1*L*T*M) := by
    calc _ = ((X:ℝ)/(2*Real.pi^2*P)) * ∑ q ∈ Icc 1 P, (q:ℝ)*|bS n q| := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q hq
          ring
      _ ≤ _ := mul_le_mul hden hsum (by positivity) (by positivity)
  have hA : (n:ℝ)*Real.exp (-(n:ℝ)/X) ≤ X := by
    have he : Real.exp (-(n:ℝ)/X) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hX0.le)
    have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) n)
    have hnXr : (n:ℝ) ≤ X := by exact_mod_cast hnX
    nlinarith
  have htail : ((n:ℝ)*Real.exp (-(n:ℝ)/X)) * (12*T/Real.sqrt P) ≤ 24*T*M*R := by
    calc _ ≤ (X:ℝ) * (12*T/Real.sqrt P) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 12*T*((X:ℝ)/Real.sqrt P) := by ring
      _ ≤ 12*T*(2*R) := mul_le_mul_of_nonneg_left hsquot (by positivity)
      _ ≤ 24*T*M*R := by
        have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ 24*T*R by positivity)
        nlinarith
  have hb := model_coefficient_error n P X hn heven hp1 hX0 (by exact_mod_cast h2p)
  have hbase : ‖fourierCoeff (Vfun X P P) (n:ℤ) -
      ((Real.exp (-(n:ℝ)/X)*(n:ℝ)*Sing n:ℝ):ℂ)‖ ≤ H*T*M*R := by
    have hh := add_le_add hbeta htail
    exact hb.trans (hh.trans_eq (by dsimp [H]; ring))
  have hdX : T ≤ D*(X:ℝ)^(η/2) := hd n X hn hnX
  have hlX : M ≤ G*(X:ℝ)^(η/2) := log_square_power (η/2) (by positivity) hX1
  calc _ ≤ H*T*M*R := hbase
    _ ≤ H*(D*(X:ℝ)^(η/2))*(G*(X:ℝ)^(η/2))*R := by gcongr
    _ = _ := by
      have he : (X:ℝ)^(η/2)*(X:ℝ)^(η/2)*(X:ℝ)^(3/4:ℝ) = (X:ℝ)^(3/4+η) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
        congr 1
        ring
      dsimp [R]
      calc _ = (H*D*G)*((X:ℝ)^(η/2)*(X:ℝ)^(η/2)*(X:ℝ)^(3/4:ℝ)) := by ring
        _ = _ := by rw [he]


/-- The zero model coefficient contributes a lower order square.
Source: P0029 page 12 main term reconstruction and page 13 display 3.8. -/
theorem model_zero_square_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 4 ≤ X →
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) 0‖^2 ≤
        C * (X:ℝ)^(2+ε) := by
  obtain ⟨C,hC,hc⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  let G : ℝ := (1+2/ε)^2
  refine ⟨(Real.pi*C)^2*G, by dsimp [G]; positivity, ?_⟩
  intro X hX
  let P := Nat.sqrt X
  obtain ⟨hp,hpX,h2p,hfour⟩ := sqrt_cutoff_bounds X hX
  have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hp0 : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlPX : Real.log (P:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpX)
  have hnorm : ‖fourierCoeff (Vfun X P P) 0‖ ≤ Real.pi*C*(X:ℝ)*(1+Real.log (X:ℝ)) := by
    calc _ = ‖∫ t, Vfun X P P t ∂haarAddCircle‖ := by simp [fourierCoeff]
      _ ≤ ∫ t, ‖Vfun X P P t‖ ∂haarAddCircle := norm_integral_le_integral_norm _
      _ ≤ Real.pi*X * ∑ q ∈ Icc 1 P, (1:ℝ)/Nat.totient q :=
        LeanLab.ExceptionalSet.PintzAlthofer2026Sup.int_norm_Vfun_le hX0 hp0.le
          (by exact_mod_cast h2p) P
      _ ≤ Real.pi*X*(C*(1+Real.log P)) :=
        mul_le_mul_of_nonneg_left (hc P) (by positivity)
      _ ≤ Real.pi*C*X*(1+Real.log (X:ℝ)) := by
        have h := mul_le_mul_of_nonneg_left (add_le_add_left hlPX 1)
          (show 0 ≤ Real.pi*C*(X:ℝ) by positivity)
        convert h using 1 <;> ring
  have hl : (1+Real.log (X:ℝ))^2 ≤ G*(X:ℝ)^ε := log_square_power ε hε hX1
  calc _ ≤ (Real.pi*C*(X:ℝ)*(1+Real.log (X:ℝ)))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (Real.pi*C)^2*(X:ℝ)^2*(1+Real.log (X:ℝ))^2 := by ring
    _ ≤ (Real.pi*C)^2*(X:ℝ)^2*(G*(X:ℝ)^ε) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by
      rw [show (X:ℝ)^2 = (X:ℝ)^(2:ℝ) by rw [Real.rpow_two]]
      calc _ = ((Real.pi*C)^2*G)*((X:ℝ)^(2:ℝ)*(X:ℝ)^ε) := by ring
        _ = _ := by rw [← Real.rpow_add hX0]


/-- LEAF. P0029 page 12, the two main term displays after 3.7, and page 13 display 3.8.
Mean square reconstruction of the even singular series from the truncated arc model.
This leaf has no zero free hypothesis and no prime generating function. -/
theorem leaf_singular_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n : ℤ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 ≤
          C * (X : ℝ) ^ (5 / 2 + ε) := by
  obtain ⟨K,hK,hk⟩ := model_coefficient_growth (ε/2) (by positivity)
  obtain ⟨Z,hZ,hz⟩ := model_zero_square_growth ε hε
  refine ⟨K^2+Z, by positivity, 4, ?_⟩
  intro X hX
  let s := (range (X+1)).filter Even
  let f : ℕ → ℝ := fun n =>
    ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) (n:ℤ) -
      ((Real.exp (-(n:ℝ)/X)*(n:ℝ)*Sing n:ℝ):ℂ)‖^2
  have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hzero : f 0 ≤ Z*(X:ℝ)^(2+ε) := by simpa [f] using hz X hX
  have hterm (n : ℕ) (hn : n ∈ s.erase 0) : f n ≤ K^2*(X:ℝ)^(3/2+ε) := by
    rcases mem_erase.mp hn with ⟨hn0,hns⟩
    rcases mem_filter.mp hns with ⟨hnr,hneven⟩
    have hnX : n ≤ X := by have := mem_range.mp hnr; omega
    have hh := hk X n hX (by omega) hneven hnX
    calc f n ≤ (K*(X:ℝ)^(3/4+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hX0.le]
        congr 2
        push_cast
        ring
  have hsub : s.erase 0 ⊆ Icc 1 X := by
    intro n hn
    rcases mem_erase.mp hn with ⟨hn0,hns⟩
    have hnr := mem_range.mp (mem_filter.mp hns).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : ((s.erase 0).card:ℝ) ≤ X := by
    have hc := card_le_card hsub
    simp only [Nat.card_Icc] at hc
    exact_mod_cast (show (s.erase 0).card ≤ X by omega)
  have hpos : (∑ n ∈ s.erase 0, f n) ≤ K^2*(X:ℝ)^(5/2+ε) := by
    calc _ ≤ ∑ n ∈ s.erase 0, K^2*(X:ℝ)^(3/2+ε) := sum_le_sum hterm
      _ = ((s.erase 0).card:ℝ)*(K^2*(X:ℝ)^(3/2+ε)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ (X:ℝ)*(K^2*(X:ℝ)^(3/2+ε)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by
        have he : (X:ℝ) * (X:ℝ)^(3/2+ε) = (X:ℝ)^(5/2+ε) := by
          calc (X:ℝ)*(X:ℝ)^(3/2+ε) = (X:ℝ)^(1:ℝ)*(X:ℝ)^(3/2+ε) := by rw [Real.rpow_one]
            _ = (X:ℝ)^((1:ℝ)+(3/2+ε)) := (Real.rpow_add hX0 _ _).symm
            _ = _ := by congr 1; ring
        calc _ = K^2*((X:ℝ)*(X:ℝ)^(3/2+ε)) := by ring
          _ = _ := by rw [he]
  have hzin : 0 ∈ s := by simp [s]
  have hsplit := sum_erase_add s f hzin
  change (∑ n ∈ s, f n) ≤ _
  rw [← hsplit]
  have hexp : (X:ℝ)^(2+ε) ≤ (X:ℝ)^(5/2+ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc _ ≤ K^2*(X:ℝ)^(5/2+ε) + Z*(X:ℝ)^(2+ε) := add_le_add hpos hzero
    _ ≤ K^2*(X:ℝ)^(5/2+ε) + Z*(X:ℝ)^(5/2+ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp hZ.le)
    _ = _ := by ring



/-- The exact mean square statement from the arc estimate and proved reconstruction.
Source: P0029 page 13 display 3.8. CONDITIONAL ON leaf_arc_energy. -/
theorem leaf_mean_square_supplied (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨Ca, hCa, Xa, ha⟩ := leaf_arc_energy Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨Cs, hCs, Xs, hs⟩ := leaf_singular_energy ε hε
  refine ⟨2 * Real.exp 2 * (Ca + Cs), max (max Xa Xs) 1, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXa : Xa ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXs : Xs ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hpow : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  have hmodel := energy_of_model X hX1
    (Vfun X (Nat.sqrt X) (Nat.sqrt X))
    (memLp_Vfun (by exact_mod_cast (show 0 < X by omega)) _ _)
    (Ca * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε))
    (Cs * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) (ha X hXa)
    ((hs X hXs).trans (mul_le_mul_of_nonneg_left hpow hCs))
  convert hmodel using 1
  ring

open Real MeasureTheory Complex
open LeanLab.PNTPort.DirichletZF

/-- Absolute convergence and a norm bound for the nonprincipal shifted Mellin line.
Source: P0029 page 11 display 3.5 and page 12 display 3.7, auxiliary contour input.
CONDITIONAL ON the source ZeroFreeBeyond hypothesis. No contour equality is asserted. -/
theorem shifted_character_kernel_integrable (Θ : ℝ) (hΘ : 1/2 ≤ Θ)
    (hZF : ZeroFreeBeyond Θ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : Θ+δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ η : ℝ, Θ+δ ≤ σ → 0 < η → σ+η ≤ 3/2 → ∀ z : ℂ, 0 < z.re →
      Integrable (fun t : ℝ =>
        (deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+I*t) /
          DirichletCharacter.LFunction χ ((σ:ℂ)+I*t)) *
        (Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t)))) ∧
      ‖∫ t : ℝ,
        (deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+I*t) /
          DirichletCharacter.LFunction χ ((σ:ℂ)+I*t)) *
        (Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t)))‖ ≤
        C * (Real.log (2*(q:ℝ)*Z) *
          (∫ t : ℝ, ‖Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t))‖) +
          (1/η) * (∫ t : ℝ, (|t|+3)^η *
            ‖Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t))‖)) := by
  obtain ⟨C,hC,hbound⟩ := Supply480.logDerivative_from_zeroFree Θ hΘ hZF δ hδ hδ1
  refine ⟨C,hC,?_⟩
  intro q inst χ hχ σ η hσ hη hση z hz
  have hhalf : 1/2 ≤ σ := by linarith
  have hupper : σ ≤ 3/2 := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hZ : 0 < Z := Z_pos
  let K : ℝ → ℂ := fun t => Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t))
  let D : ℝ → ℂ := fun t => deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+I*t) /
    DirichletCharacter.LFunction χ ((σ:ℂ)+I*t)
  let a : ℝ := Real.log (2*(q:ℝ)*Z)
  let M : ℝ → ℝ := fun t => a*‖K t‖ + Real.log (|t|+3)*‖K t‖
  have hK : Integrable K := Supply480.gamma_mellin_kernel_integrable σ hhalf hupper z hz
  obtain ⟨hW,hWbound⟩ := Supply480.gamma_mellin_kernel_log_weight σ η hhalf hη hση z hz
  have hM : Integrable M := (hK.norm.const_mul a).add hW
  have hCM : Integrable (fun t => C*M t) := hM.const_mul C
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hderiv : Continuous (deriv (DirichletCharacter.LFunction χ)) :=
    continuous_iff_continuousAt.mpr (fun s => (hf.analyticAt s).deriv.continuousAt)
  have hpath : Continuous (fun t : ℝ => (σ:ℂ)+I*t) := by fun_prop
  have hnonzero (t : ℝ) : DirichletCharacter.LFunction χ ((σ:ℂ)+I*t) ≠ 0 := by
    by_cases ht : (σ:ℂ)+I*t = 1
    · rw [ht]
      exact DirichletCharacter.LFunction_apply_one_ne_zero hχ
    · exact hZF q χ _ (by simpa using (show Θ < σ by linarith)) ht
  have hD : Continuous D := (hderiv.comp hpath).div (hf.continuous.comp hpath) hnonzero
  have hpoint (t : ℝ) : ‖D t*K t‖ ≤ C*M t := by
    have hb := hbound q χ hχ σ t hσ (by linarith)
    have hlog : Real.log (Bt q t) = a + Real.log (|t|+3) := by
      dsimp [a, Bt]
      rw [show 2*(q:ℝ)*(|t|+3)*Z = (2*(q:ℝ)*Z)*(|t|+3) by ring,
        Real.log_mul (by positivity) (by linarith [abs_nonneg t])]
    rw [hlog] at hb
    rw [norm_mul]
    calc _ ≤ (C*(a+Real.log (|t|+3)))*‖K t‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by dsimp [M]; ring
  have hi : Integrable (fun t => D t*K t) :=
    hCM.mono' (hD.aestronglyMeasurable.mul hK.aestronglyMeasurable) (ae_of_all _ hpoint)
  refine ⟨hi,?_⟩
  calc _ ≤ ∫ t : ℝ, C*M t :=
      (norm_integral_le_integral_norm _).trans
        (integral_mono_ae hi.norm hCM (ae_of_all _ hpoint))
    _ = C * (a*(∫ t : ℝ, ‖K t‖) + ∫ t : ℝ, Real.log (|t|+3)*‖K t‖) := by
      dsimp only [M]
      rw [integral_const_mul, integral_add (hK.norm.const_mul a) hW, integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hWbound) hC.le


open Real Complex MeasureTheory Filter Topology

/-- A vertical contour can be moved when the horizontal boundary integrals vanish.
Source: P0029 page 11 display 3.5, derived contour bookkeeping.
CONDITIONAL ON the explicit strip and limit hypotheses. -/
theorem vertical_integral_eq_of_horizontal_decay (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => f ((b:ℂ)+t*I)))
    (hbottom : Tendsto (fun T : ℝ => ∫ σ in a..b, f ((σ:ℂ)-T*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ σ in a..b, f ((σ:ℂ)+T*I)) atTop (𝓝 0)) :
    (∫ t : ℝ, f ((a:ℂ)+t*I)) = ∫ t : ℝ, f ((b:ℂ)+t*I) := by
  have hrect (T : ℝ) :
      (∫ σ in a..b, f ((σ:ℂ)-T*I)) - (∫ σ in a..b, f ((σ:ℂ)+T*I)) +
        I • (∫ t in (-T)..T, f ((b:ℂ)+t*I)) -
        I • (∫ t in (-T)..T, f ((a:ℂ)+t*I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a:ℂ)-T*I) ((b:ℂ)+T*I) (by
        intro z hz
        have hre : a ≤ z.re ∧ z.re ≤ b := by
          have hr := hz.1
          simpa [Set.uIcc_of_le hab] using hr
        exact (hdiff z hre.1 hre.2).differentiableWithinAt)
    simpa [sub_eq_add_neg] using h
  have hla := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hlb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ =>
      (∫ σ in a..b, f ((σ:ℂ)-T*I)) - (∫ σ in a..b, f ((σ:ℂ)+T*I)) +
        I • (∫ t in (-T)..T, f ((b:ℂ)+t*I)) -
        I • (∫ t in (-T)..T, f ((a:ℂ)+t*I))) atTop
      (𝓝 ((0:ℂ)-0 + I • (∫ t : ℝ, f ((b:ℂ)+t*I)) -
        I • (∫ t : ℝ, f ((a:ℂ)+t*I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.smul hlb)).sub
      (tendsto_const_nhds.smul hla)
  have hzlim : Tendsto (fun T : ℝ =>
      (∫ σ in a..b, f ((σ:ℂ)-T*I)) - (∫ σ in a..b, f ((σ:ℂ)+T*I)) +
        I • (∫ t in (-T)..T, f ((b:ℂ)+t*I)) -
        I • (∫ t in (-T)..T, f ((a:ℂ)+t*I))) atTop (𝓝 0) := by
    have he : (fun T : ℝ =>
        (∫ σ in a..b, f ((σ:ℂ)-T*I)) - (∫ σ in a..b, f ((σ:ℂ)+T*I)) +
          I • (∫ t in (-T)..T, f ((b:ℂ)+t*I)) -
          I • (∫ t in (-T)..T, f ((a:ℂ)+t*I))) = fun _ => 0 := funext hrect
    rw [he]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hzlim
  have hmul : I * ((∫ t : ℝ, f ((b:ℂ)+t*I)) - ∫ t : ℝ, f ((a:ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul, mul_sub] using heq
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left I_ne_zero)).symm

/-- Uniform strip decay makes the horizontal boundary terms vanish.
Source: P0029 page 11 display 3.5, derived contour bookkeeping.
CONDITIONAL ON the explicit strip and decay hypotheses. -/
theorem vertical_integral_eq_of_strip_decay (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => f ((b:ℂ)+t*I)))
    (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hbound : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, ‖f ((σ:ℂ)+t*I)‖ ≤ g |t|) :
    (∫ t : ℝ, f ((a:ℂ)+t*I)) = ∫ t : ℝ, f ((b:ℂ)+t*I) := by
  have hdec : Tendsto (fun T : ℝ => g |T| * |b-a|) atTop (𝓝 0) := by
    simpa using (hg.comp tendsto_abs_atTop_atTop).mul_const |b-a|
  apply vertical_integral_eq_of_horizontal_decay f a b hab hdiff ha hb
  · apply squeeze_zero_norm (fun T => ?_) hdec
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    simp only [Set.uIoc_of_le hab, Set.mem_Ioc] at hσ
    have h := hbound σ ⟨hσ.1.le,hσ.2⟩ (-T)
    simpa [sub_eq_add_neg] using h
  · apply squeeze_zero_norm (fun T => ?_) hdec
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    simp only [Set.uIoc_of_le hab, Set.mem_Ioc] at hσ
    exact hbound σ ⟨hσ.1.le,hσ.2⟩ T


/-- Uniform horizontal decay of the nonprincipal Gamma logarithmic derivative kernel.
Source: P0029 page 11 display 3.5 and page 12 display 3.7, contour edge bound.
CONDITIONAL ON the source ZeroFreeBeyond hypothesis. -/
theorem character_kernel_strip_bound (Θ : ℝ) (hΘ : 1/2 ≤ Θ) (hZF : ZeroFreeBeyond Θ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : Θ+δ ≤ 1)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a b : ℝ) (hleft : Θ+δ ≤ a) (hab : a ≤ b) (hb : b ≤ 3/2)
    (z : ℂ) (hz : 0 < z.re) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖(deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+I*t) /
          DirichletCharacter.LFunction χ ((σ:ℂ)+I*t)) *
        (Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t)))‖ ≤
          K * (|t|+3)^2 * Real.exp (-((Real.pi/2-|Complex.arg z|)*|t|)) := by
  obtain ⟨C,hC,hbound⟩ := Supply480.logDerivative_from_zeroFree Θ hΘ hZF δ hδ hδ1
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0:ℝ) < q := zero_lt_one.trans_le hq1
  have hZ : 0 < Z := Z_pos
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let L : ℝ := Real.log (2*(q:ℝ)*Z)
  let R : ℝ := ‖z‖^(-a) + ‖z‖^(-b)
  let G : ℝ := Real.exp (5/2) * Real.sqrt (2*Real.pi)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    have hm : (1:ℝ) ≤ (q:ℝ)*Z := by
      simpa using mul_le_mul hq1 one_le_Z zero_le_one (Nat.cast_nonneg (α:=ℝ) q)
    nlinarith only [hm]
  have hR : 0 < R := add_pos (Real.rpow_pos_of_pos hnz _) (Real.rpow_pos_of_pos hnz _)
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨C*(L+1)*G*R, by positivity, ?_⟩
  intro σ hσ t
  rcases hσ with ⟨hσa,hσb⟩
  have hhalf : 1/2 ≤ σ := by linarith
  have hupper : σ ≤ 3/2 := hσb.trans hb
  have hRP : ‖z‖^(-σ) ≤ R := by
    by_cases hzn : 1 ≤ ‖z‖
    · exact (Real.rpow_le_rpow_of_exponent_le hzn (by linarith only [hσa])).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg z) _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hnz (le_of_not_ge hzn) (by linarith only [hσb])).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg z) _))
  have hB : (1:ℝ) ≤ |t|+3 := by linarith [abs_nonneg t]
  have hpow : (|t|+3)^(σ-1/2) ≤ |t|+3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB (show σ-1/2 ≤ 1 by linarith)
  have hlog : Real.log (Bt q t) ≤ (L+1)*(|t|+3) := by
    have heq : Real.log (Bt q t) = L+Real.log (|t|+3) := by
      dsimp [L, Bt]
      rw [show 2*(q:ℝ)*(|t|+3)*Z = (2*(q:ℝ)*Z)*(|t|+3) by ring,
        Real.log_mul (by positivity) (by linarith [abs_nonneg t])]
    rw [heq]
    have hl : Real.log (|t|+3) ≤ |t|+3 :=
      (Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t])).trans (sub_le_self _ zero_le_one)
    have hm := mul_le_mul_of_nonneg_left hB hL
    nlinarith only [hl,hm]
  have hD : ‖deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+I*t) /
      DirichletCharacter.LFunction χ ((σ:ℂ)+I*t)‖ ≤ C*(L+1)*(|t|+3) := by
    calc _ ≤ C*Real.log (Bt q t) := hbound q χ hχ σ t (hleft.trans hσa) (by linarith)
      _ ≤ C*((L+1)*(|t|+3)) := mul_le_mul_of_nonneg_left hlog hC.le
      _ = _ := by ring
  have hg := (Supply480.gamma_mellin_kernel_bound σ hhalf hupper z hz).2 t
  have hkernel : ‖Complex.Gamma ((σ:ℂ)+I*t) * z^(-((σ:ℂ)+I*t))‖ ≤
      G*R*(|t|+3)*Real.exp (-((Real.pi/2-|Complex.arg z|)*|t|)) := by
    refine hg.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hRP hG.le) hpow (by positivity) (by positivity)
  rw [norm_mul]
  exact (mul_le_mul hD hkernel (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The nonprincipal logarithmic derivative Mellin contour shifts inside the zero free strip.
Source: P0029 page 11 display 3.5 and page 12 display 3.7.
CONDITIONAL ON the source ZeroFreeBeyond hypothesis. -/
theorem nonprincipal_contour_shift (Θ : ℝ) (hΘ : 1/2 ≤ Θ) (hZF : ZeroFreeBeyond Θ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : Θ+δ ≤ 1)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a b : ℝ) (hleft : Θ+δ ≤ a) (hab : a ≤ b) (hb : b < 3/2)
    (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ, (deriv (DirichletCharacter.LFunction χ) ((a:ℂ)+t*I) /
      DirichletCharacter.LFunction χ ((a:ℂ)+t*I)) *
      (Complex.Gamma ((a:ℂ)+t*I) * z^(-((a:ℂ)+t*I)))) =
    ∫ t : ℝ, (deriv (DirichletCharacter.LFunction χ) ((b:ℂ)+t*I) /
      DirichletCharacter.LFunction χ ((b:ℂ)+t*I)) *
      (Complex.Gamma ((b:ℂ)+t*I) * z^(-((b:ℂ)+t*I))) := by
  let f : ℂ → ℂ := fun s => (deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (Complex.Gamma s * z^(-s))
  let d : ℝ := Real.pi/2-|Complex.arg z|
  have hd : 0 < d := by
    have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    dsimp [d]
    linarith
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hf := DirichletCharacter.differentiable_LFunction hχ
  have hdiff (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) : DifferentiableAt ℂ f s := by
    have hpos : 0 < s.re := by linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      by_cases hs : s = 1
      · rw [hs]
        exact DirichletCharacter.LFunction_apply_one_ne_zero hχ
      · exact hZF q χ s (by linarith) hs
    have hΓ : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s (by
      intro m hm
      have he := congrArg Complex.re hm
      simp at he
      linarith [Nat.cast_nonneg (α:=ℝ) m])
    have hp : DifferentiableAt ℂ (fun w : ℂ => z^(-w)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hz0)
    exact (((hf.analyticAt s).deriv.differentiableAt).div (hf s) hL).mul (hΓ.mul hp)
  obtain ⟨C,hC,hline⟩ := shifted_character_kernel_integrable Θ hΘ hZF δ hδ hδ1
  let η : ℝ := (3/2-b)/2
  have hη : 0 < η := by dsimp [η]; linarith
  have haη : a+η ≤ 3/2 := by dsimp [η]; linarith
  have hbη : b+η ≤ 3/2 := by dsimp [η]; linarith
  have hia : Integrable (fun t : ℝ => f ((a:ℂ)+t*I)) := by
    simpa only [f, mul_comm I] using (hline q χ hχ a η hleft hη haη z hz).1
  have hib : Integrable (fun t : ℝ => f ((b:ℂ)+t*I)) := by
    simpa only [f, mul_comm I] using (hline q χ hχ b η (hleft.trans hab) hη hbη z hz).1
  obtain ⟨K,hK,hkernel⟩ := character_kernel_strip_bound Θ hΘ hZF δ hδ hδ1
    q χ hχ a b hleft hab hb.le z hz
  let g : ℝ → ℝ := fun T => K*(T+3)^2*Real.exp (-(d*T))
  have hshift : Tendsto (fun T : ℝ => T+3) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [eventually_ge_atTop (r-3)] with T hT
    linarith
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) d hd).comp hshift
  have hg : Tendsto g atTop (𝓝 0) := by
    have hh := hbase.const_mul (K*Real.exp (3*d))
    convert hh using 1
    · funext T
      dsimp [g]
      rw [Real.rpow_two]
      have he : Real.exp (3*d)*Real.exp (-(d*(T+3))) = Real.exp (-(d*T)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc K*(T+3)^2*Real.exp (-(d*T)) =
          K*(T+3)^2*(Real.exp (3*d)*Real.exp (-(d*(T+3)))) := by rw [he]
        _ = _ := by ring
    · simp
  have hbd : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, ‖f ((σ:ℂ)+t*I)‖ ≤ g |t| := by
    intro σ hσ t
    simpa only [f, g, d, mul_comm I] using hkernel σ hσ t
  exact vertical_integral_eq_of_strip_decay f a b hab hdiff hia hib g hg hbd


open Set

/-- The Gamma Laplace integral converges for a complex rate of positive real part.
Source: P0029 page 10 display 3.3 and page 11 display 3.5. -/
theorem gamma_laplace_integrable (s z : ℂ) (hs : 0 < s.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1)*Complex.exp (-(z*t))) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t^(s.re-1)*Real.exp (-(z.re*t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := s.re-1) (p := 1) (b := z.re) (by linarith) (by norm_num) hz
  have hm : Measurable (fun t : ℝ => (t:ℂ)^(s-1)*Complex.exp (-(z*t))) := by fun_prop
  apply hg.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The Gamma Laplace integral is differentiable in its complex rate in the right half plane.
Source: P0029 page 10 display 3.3 and page 11 display 3.5, off center Mellin input. -/
theorem gamma_laplace_differentiable (s z : ℂ) (hs : 0 < s.re) (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ =>
      ∫ t : ℝ in Set.Ioi 0, (t:ℂ)^(s-1)*Complex.exp (-(w*t))) z := by
  let c : ℝ := z.re/2
  have hc : 0 < c := half_pos hz
  let F : ℂ → ℝ → ℂ := fun w t => (t:ℂ)^(s-1)*Complex.exp (-(w*t))
  let F' : ℂ → ℝ → ℂ := fun w t => (t:ℂ)^(s-1)*Complex.exp (-(w*t))*(-(t:ℂ))
  let B : ℝ → ℝ := fun t => t^s.re*Real.exp (-(c*t))
  have hF : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Set.Ioi 0)) := by
    apply Eventually.of_forall
    intro w
    have hm : Measurable (F w) := by dsimp [F]; fun_prop
    exact hm.aestronglyMeasurable
  have hFi : Integrable (F z) (volume.restrict (Set.Ioi 0)) := gamma_laplace_integrable s z hs hz
  have hF' : AEStronglyMeasurable (F' z) (volume.restrict (Set.Ioi 0)) := by
    have hm : Measurable (F' z) := by dsimp [F']; fun_prop
    exact hm.aestronglyMeasurable
  have hBi : Integrable B (volume.restrict (Set.Ioi 0)) := by
    change IntegrableOn (fun t : ℝ => t^s.re*Real.exp (-(c*t))) (Set.Ioi 0)
    simpa only [Real.rpow_one, neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := s.re) (p := 1) (b := c) (by linarith) (by norm_num) hc
  have hbd : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi 0),
      ∀ w ∈ Metric.ball z c, ‖F' w t‖ ≤ B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have hdist : |w.re-z.re| < c := by
      simpa using (Complex.abs_re_le_norm (w-z)).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hw)
    have hlow : c ≤ w.re := by
      have hh := (abs_lt.mp hdist).1
      dsimp [c] at hh ⊢
      linarith
    have hn : ‖F' w t‖ = t^s.re*Real.exp (-(w.re*t)) := by
      dsimp [F']
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp,
        norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hp : t^(s.re-1)*t = t^s.re := by
        rw [Real.rpow_sub_one ht.ne']
        exact div_mul_cancel₀ _ ht.ne'
      calc _ = (t^(s.re-1)*t)*Real.exp (-(w.re*t)) := by ring
        _ = _ := by rw [hp]
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hlow ht.le)))
      (Real.rpow_nonneg ht.le _)
  have hder : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi 0),
      ∀ w ∈ Metric.ball z c, HasDerivAt (fun w => F w t) (F' w t) w := by
    apply Eventually.of_forall
    intro t w hw
    convert ((((hasDerivAt_id w).mul_const (t:ℂ)).neg).cexp).const_mul ((t:ℂ)^(s-1)) using 1 <;>
      dsimp [F,F'] <;> ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hc) hF hFi hF' hbd hBi hder).2.differentiableAt



end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
