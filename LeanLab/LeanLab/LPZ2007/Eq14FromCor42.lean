/-
P0045 Languasco, Pintz, Zaccagnini 2007, Section 4 p.6-7, displays (11) to (15): the repaired (25)
cut down to Corollary 4.2, Lemma 6.2 and the arithmetic of (16) to (24).

Unit U-6823, CLOUD 20261021T0217Z-cloud56, track T2, idea I-0091. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics, the paper's own Section 4. Binary Goldbach is
OPEN; nothing here is Goldbach.

* `RMpp_expand`, `RMpp_eq_tk'`: the finite expansion of `G^k`,
  `R''_𝔐(N) = Σ_ν R_𝔐(N − 2^{ν_1} − … − 2^{ν_k}) = Σ_n t'_k(N − n) R_𝔐(n)`. PROVED.
* `split_bound`: (11) plus (12), `|R''_𝔐 − R^(3)| ≤ η R^(3) + (B + 1) Σ_{J₂} n 𝔖(n)`. PROVED.
* `J2_bound`: (12) to (14), the `J₂(X)` part `Σ_{J₂} 𝔖(n) ≤ K L^{k−1} ε L`, CONDITIONAL ON the
  bound `A(m, s) ≤ ε L` of Lemma 6.2 for the moduli `s = r'/(r', C*)`. PROVED as an implication.
* `eq25_twoC0_of_cor42`: the repaired (25), CONDITIONAL ON `Cor42W`, `Lemma62` and `R3Asymp`.
* `mainJ_twoC0_of_cor42`, `main_19_24_of_cor42`: the repaired Theorem and the I-0091 shape with
  `eq25_twoC0` replaced by these three named inputs; the cited sorry `eq25_twoC0` is not used.

Two encoding points, stated honestly.
1. `Cor42W` is Corollary 4.2 on the window `n ∈ [X/2, X]` in place of `J(X) = [2X/3, X]`. The paper
   applies Corollary 4.2 at `n = N − 2^{ν_1} − … − 2^{ν_k}` with `N ∈ J(X)`, and such `n` can lie
   just below `2X/3`, by up to `k X 2^{−√L}`; so the step as printed needs the Corollary a little
   beyond `J(X)`. `cor42_of_cor42W` shows `Cor42W` implies the cited `Cor42`.
2. `R3Asymp` is the content of (15) to (24) with the factor `2c0` of F-0038:
   `R^(3)_k(N) = Σ_ν n_ν 𝔖(n_ν) = 2c0 C(k, N) N L^k + o(N L^k)` uniformly in even `N ∈ J(X)`.
-/
import Mathlib
import LeanLab.LPZ2007.Eq3Reduce
import LeanLab.LPZ2007.RgUpperProof
import LeanLab.LPZ2007.MinorBoundProof
import LeanLab.LPZ2007.Corollary
import LeanLab.LPZ2007.Lemma62Port

namespace LeanLab.LPZ2007.Eq14FromCor42

open Finset Real MeasureTheory LeanLab.LPZ2007 LeanLab.LPZ2007.MinorBessel
open LeanLab.LPZ2007.Eq3Reduce

noncomputable section

/-! ### Step 1: the finite expansion of `G^k` -/

/-- `R''_𝔐(N) = Σ_{ν ∈ [1, L']^k} R_𝔐(N − 2^{ν_1} − … − 2^{ν_k})`, when the major arcs are
bounded and every `2^{ν_1} + … + 2^{ν_k} ≤ N`. -/
theorem RMpp_expand (k : ℕ) {X P : ℝ} (hP : 0 < P) (hPX : P * (P + 1) ≤ X) (N : ℕ)
    (hN : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    RMpp k X P N = ∑ ν ∈ tuples k ⌊Lp X⌋₊, RM X P (N - pow2sum ν) := by
  unfold RMpp RM
  have hpt : ∀ α : ℝ, Sx X α ^ 2 * Gx X α ^ k * e (-(N * α)) =
      ∑ ν ∈ tuples k ⌊Lp X⌋₊, Sx X α ^ 2 * e (-(((N - pow2sum ν : ℕ) : ℝ) * α)) := by
    intro α
    rw [Gx_pow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [mul_assoc, e_add, Nat.cast_sub (hN ν hν)]
    congr 2; ring
  simp_rw [hpt]
  have hsub := majorArcs_subset hP hPX
  rw [integral_finset_sum]
  intro ν _
  exact ((continuous_Sx X).pow 2 |>.mul (continuous_e.comp (by fun_prop))).integrableOn_Icc.mono_set
    hsub

/-- The fibre form of a sum over `ν`: `Σ_ν f(N − pow2sum ν) = Σ_{n ≤ N} t'_k(N − n) f(n)`. -/
theorem sum_tuples_eq_tk' {β : Type*} [AddCommMonoid β] (k : ℕ) (X : ℝ) (N : ℕ) (f : ℕ → β)
    (hN : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    ∑ ν ∈ tuples k ⌊Lp X⌋₊, f (N - pow2sum ν) = ∑ n ∈ range (N + 1), tk' k X (N - n) • f n := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ν => N - pow2sum ν) (t := range (N + 1))
    (fun ν _ => by simp only [mem_range]; omega)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [Finset.sum_congr rfl (g := fun _ => f n) (fun ν hν => by rw [(mem_filter.1 hν).2]),
    sum_const]
  congr 1
  unfold tk'
  congr 1
  ext ν
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by have := hN ν h1; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by have := hN ν h1; omega⟩

/-- Step 1 in the paper's form: `R''_𝔐(N) = Σ_{n ≤ N} t'_k(N − n) R_𝔐(n)`. -/
theorem RMpp_eq_tk' (k : ℕ) {X P : ℝ} (hP : 0 < P) (hPX : P * (P + 1) ≤ X) (N : ℕ)
    (hN : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    RMpp k X P N = ∑ n ∈ range (N + 1), (tk' k X (N - n) : ℂ) * RM X P n := by
  rw [RMpp_expand k hP hPX N hN, sum_tuples_eq_tk' k X N _ hN]
  simp only [nsmul_eq_mul]

/-! ### Step 2: (11), (12) and (14) -/

/-- `𝔖(n) ≥ 0`. -/
theorem sing_nonneg (n : ℕ) : 0 ≤ sing n := by
  unfold sing
  refine tprod_nonneg fun p => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  split_ifs
  · exact div_nonneg (by linarith) (by linarith)
  · have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h1
    linarith

/-- `R^(3)_k(N) = Σ_{ν ∈ [1, L']^k} n_ν 𝔖(n_ν)`, `n_ν = N − 2^{ν_1} − … − 2^{ν_k}`, (15) p.7. -/
def R3 (k : ℕ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ ν ∈ tuples k ⌊Lp X⌋₊, ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν)

theorem R3_nonneg (k : ℕ) (X : ℝ) (N : ℕ) : 0 ≤ R3 k X N :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sing_nonneg _)

/-- (15) p.7 in the paper's form: `R^(3)_k(N) = Σ_{n ≤ N} t'_k(N − n) 𝔖(n) n`. -/
theorem R3_eq_tk' (k : ℕ) (X : ℝ) (N : ℕ) (hN : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    R3 k X N = ∑ n ∈ range (N + 1), (tk' k X (N - n) : ℝ) * ((n : ℝ) * sing n) := by
  unfold R3
  rw [sum_tuples_eq_tk' k X N (fun n => (n : ℝ) * sing n) hN]
  simp only [nsmul_eq_mul]

/-- `n` avoids the exceptional moduli: `r ∤ C* n` for all `r`, condition (9) p.6. -/
def Good (rs : Finset ℕ) (Cstar n : ℕ) : Prop := ∀ r ∈ rs, ¬ r ∣ Cstar * n

open Classical in
/-- (11) and (12): `|R''_𝔐 − R^(3)| ≤ η R^(3) + (B + 1) Σ_{n_ν ∈ J₂} n_ν 𝔖(n_ν)`. -/
theorem split_bound (k : ℕ) (X P : ℝ) (N Cstar : ℕ) (rs : Finset ℕ) {η B : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hg : ∀ ν ∈ tuples k ⌊Lp X⌋₊, Good rs Cstar (N - pow2sum ν) →
      ‖RM X P (N - pow2sum ν) - ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν)‖ ≤
        η * ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν))
    (ha : ∀ ν ∈ tuples k ⌊Lp X⌋₊,
      ‖RM X P (N - pow2sum ν)‖ ≤ B * ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν)) :
    ‖(∑ ν ∈ tuples k ⌊Lp X⌋₊, RM X P (N - pow2sum ν)) - ((R3 k X N : ℝ) : ℂ)‖ ≤
      η * R3 k X N + (B + 1) * ∑ ν ∈ (tuples k ⌊Lp X⌋₊).filter
        (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
          ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) := by
  unfold R3
  rw [Complex.ofReal_sum, ← sum_sub_distrib, sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ν hν => ?_)
  set a : ℝ := ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) with ha_def
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (sing_nonneg _)
  have hac : ((a : ℝ) : ℂ) = (((N - pow2sum ν : ℕ) : ℝ) : ℂ) * ((sing (N - pow2sum ν) : ℝ) : ℂ) := by
    rw [ha_def]; push_cast; ring
  by_cases hG : Good rs Cstar (N - pow2sum ν)
  · rw [if_neg (not_not.2 hG), mul_zero, add_zero]
    have := hg ν hν hG
    rw [show η * ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) = η * a by rw [ha_def]; ring]
      at this
    rw [hac]; exact this
  · rw [if_pos hG]
    have h1 := ha ν hν
    have h2 : ‖RM X P (N - pow2sum ν) - ((a : ℝ) : ℂ)‖ ≤ ‖RM X P (N - pow2sum ν)‖ + a := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    rw [show B * ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) = B * a by rw [ha_def]; ring]
      at h1
    nlinarith [mul_nonneg hB ha0, mul_nonneg hη ha0]

/-- `2^{ν_1} + … + 2^{ν_k} ≤ k 2^M` on `[1, M]^k`. -/
theorem pow2sum_le {k M : ℕ} {ν : Fin k → ℕ} (hν : ν ∈ tuples k M) : pow2sum ν ≤ k * 2 ^ M := by
  unfold pow2sum
  simp only [tuples, Fintype.mem_piFinset, mem_Icc] at hν
  calc ∑ i, 2 ^ ν i ≤ ∑ _i : Fin k, 2 ^ M :=
        sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (hν i).2
    _ = k * 2 ^ M := by simp

theorem even_pow2sum {k M : ℕ} {ν : Fin k → ℕ} (hν : ν ∈ tuples k M) : Even (pow2sum ν) := by
  unfold pow2sum
  simp only [tuples, Fintype.mem_piFinset, mem_Icc] at hν
  exact Finset.even_sum _ fun i _ => (Nat.even_pow).2 ⟨even_two, by have := (hν i).1; omega⟩

theorem pow2sum_cons {j : ℕ} (a : ℕ) (t : Fin j → ℕ) :
    pow2sum (Fin.cons a t : Fin (j + 1) → ℕ) = 2 ^ a + pow2sum t := by
  unfold pow2sum; rw [Fin.sum_univ_succ]; simp

/-- Splitting off the first exponent, "exploiting the symmetry" p.7. -/
theorem sum_tuples_succ {β : Type*} [AddCommMonoid β] (j M : ℕ) (F : (Fin (j + 1) → ℕ) → β) :
    ∑ ν ∈ tuples (j + 1) M, F ν = ∑ t ∈ tuples j M, ∑ a ∈ Icc 1 M, F (Fin.cons a t) := by
  rw [← Finset.sum_product' (f := fun t a => F (Fin.cons a t))]
  refine Finset.sum_bij' (fun ν _ => (Fin.tail ν, ν 0)) (fun x _ => Fin.cons x.2 x.1) ?_ ?_ ?_ ?_ ?_
  · intro ν hν
    simp only [tuples, mem_product, Fintype.mem_piFinset] at hν ⊢
    exact ⟨fun i => hν i.succ, hν 0⟩
  · intro x hx
    simp only [tuples, mem_product, Fintype.mem_piFinset] at hx ⊢
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hx.2
    · simpa using hx.1 i
  · intro ν _; simp
  · intro x _; simp
  · intro ν _; simp

open Classical in
/-- (12) to (14), the `J₂(X)` part: if every exceptional `r` gives a modulus `s(r)` with
`r ∣ C* n ⟹ s(r) ∣ n` and `A(m, s(r)) ≤ ε L` on `m ∈ [X/2, X]`, the `n_ν ∈ J₂` contribute
`Σ 𝔖(n_ν) ≤ K M^{k−1} ε L`, `M = ⌊L'⌋`, `K = |rs|`. -/
theorem J2_bound (j : ℕ) (X : ℝ) (N Cstar : ℕ) (rs : Finset ℕ) (s : ℕ → ℕ) (ε : ℝ)
    (hs : ∀ r ∈ rs, ∀ n : ℕ, r ∣ Cstar * n → s r ∣ n)
    (hA : ∀ r ∈ rs, ∀ m : ℕ, X / 2 ≤ m → (m : ℝ) ≤ X → Amr X m (s r) ≤ ε * Lg X)
    (hNX : (N : ℝ) ≤ X)
    (hlt : ∀ ν ∈ tuples (j + 1) ⌊Lp X⌋₊, pow2sum ν < N)
    (hwin : ∀ t ∈ tuples j ⌊Lp X⌋₊, X / 2 ≤ ((N - pow2sum t : ℕ) : ℝ)) :
    ∑ ν ∈ (tuples (j + 1) ⌊Lp X⌋₊).filter (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
        sing (N - pow2sum ν) ≤ rs.card * (⌊Lp X⌋₊ : ℝ) ^ j * (ε * Lg X) := by
  set M := ⌊Lp X⌋₊
  -- pointwise: a bad `n` is caught by some `s(r)`
  have hpt : ∀ ν ∈ tuples (j + 1) M, (if ¬ Good rs Cstar (N - pow2sum ν) then
      sing (N - pow2sum ν) else 0) ≤
      ∑ r ∈ rs, if s r ∣ N - pow2sum ν then sing (N - pow2sum ν) else 0 := by
    intro ν _
    by_cases hG : Good rs Cstar (N - pow2sum ν)
    · rw [if_neg (not_not.2 hG)]
      exact sum_nonneg fun r _ => by split_ifs <;> simp [sing_nonneg]
    · rw [if_pos hG]
      unfold Good at hG; push_neg at hG
      obtain ⟨r, hr, hdvd⟩ := hG
      have := Finset.single_le_sum (f := fun r => if s r ∣ N - pow2sum ν then
        sing (N - pow2sum ν) else 0) (fun r _ => by split_ifs <;> simp [sing_nonneg]) hr
      simpa [hs r hr _ hdvd] using this
  rw [sum_filter]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_comm]
  have hcard : (tuples j M).card = M ^ j := by
    simp [tuples, Fintype.card_piFinset]
  calc ∑ r ∈ rs, ∑ ν ∈ tuples (j + 1) M, (if s r ∣ N - pow2sum ν then sing (N - pow2sum ν) else 0)
      ≤ ∑ _r ∈ rs, ((M : ℝ) ^ j * (ε * Lg X)) := by
        refine sum_le_sum fun r hr => ?_
        rw [sum_tuples_succ]
        have : ∀ t ∈ tuples j M, ∑ a ∈ Icc 1 M, (if s r ∣ N - pow2sum (Fin.cons a t : Fin (j + 1) → ℕ)
            then sing (N - pow2sum (Fin.cons a t : Fin (j + 1) → ℕ)) else 0) ≤ ε * Lg X := by
          intro t ht
          set m := N - pow2sum t with hm
          have hcons : ∀ a ∈ Icc 1 M, (Fin.cons a t : Fin (j + 1) → ℕ) ∈ tuples (j + 1) M := by
            intro a ha
            simp only [tuples, Fintype.mem_piFinset] at ht ⊢
            intro i; refine Fin.cases ?_ (fun i => ?_) i
            · simpa using ha
            · simpa using ht i
          have heq : ∀ a ∈ Icc 1 M, N - pow2sum (Fin.cons a t : Fin (j + 1) → ℕ) = m - 2 ^ a := by
            intro a _; rw [pow2sum_cons, hm]; omega
          have hlt' : ∀ a ∈ Icc 1 M, 2 ^ a < m := by
            intro a ha; have := hlt _ (hcons a ha); rw [pow2sum_cons] at this; rw [hm]; omega
          have hmX : (m : ℝ) ≤ X := by
            have : m ≤ N := Nat.sub_le _ _
            exact le_trans (by exact_mod_cast this) hNX
          refine le_trans (le_of_eq ?_) (hA r hr m (hwin t ht) hmX)
          unfold Amr
          rw [sum_filter]
          refine sum_congr rfl fun a ha => ?_
          rw [heq a ha]
          simp only [hlt' a ha, true_and]
        refine (sum_le_sum this).trans ?_
        rw [sum_const, hcard, nsmul_eq_mul]; push_cast; rfl
    _ = rs.card * (M : ℝ) ^ j * (ε * Lg X) := by rw [sum_const, nsmul_eq_mul]; ring

/-! ### Step 3: the named inputs and the repaired (25) -/

/-- Corollary 4.2 p.6 on the window `n ∈ [X/2, X]`, see the header, point 1. -/
def Cor42W : Prop :=
  ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → ∃ (Cstar C1 : ℕ) (c B X0 : ℝ), 1 ≤ Cstar ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X → ∃ P : ℝ, PRange X P ∧ ∃ rs : Finset ℕ, rs.card ≤ C1 ∧
      (∀ r ∈ rs, c * Lg X ^ 2 ≤ oddRad r) ∧
      (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X → (∀ r ∈ rs, ¬ r ∣ Cstar * n) →
        ‖RM X P n - n * sing n‖ ≤ η * n * sing n) ∧
      (∀ n : ℕ, Even n → X / 2 ≤ n → (n : ℝ) ≤ X → ‖RM X P n‖ ≤ B * n * sing n)

theorem cor42_of_cor42W (h : Cor42W) : Cor42 := by
  obtain ⟨η0, hη0, H⟩ := h
  refine ⟨η0, hη0, fun η hη hηl => ?_⟩
  obtain ⟨Cs, C1, c, B, X0, hCs, hc, HX⟩ := H η hη hηl
  refine ⟨Cs, C1, c, B, max X0 0, hCs, hc, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := (le_max_right _ _).trans hX
  obtain ⟨P, hP, rs, h1, h2, h3, h4⟩ := HX X ((le_max_left _ _).trans hX)
  have hw : ∀ n : ℕ, InJ X n → X / 2 ≤ n := fun n hn => by have := hn.1; linarith
  exact ⟨P, hP, rs, h1, h2, fun n he hJ hr => h3 n he (hw n hJ) hJ.2 hr,
    fun n he hJ => h4 n he (hw n hJ) hJ.2⟩

/-- (15) to (24) with the factor `2c0` of F-0038: `R^(3)_k(N) = 2c0 C(k, N) N L^k + o(N L^k)`
uniformly in even `N ∈ J(X)`. A named input, the arithmetic part of Section 4. -/
def R3Asymp : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
    |R3 k X N - twoC0 * Ckn k N * N * Lg X ^ k| ≤ η * N * Lg X ^ k

theorem oddRad_odd (r : ℕ) : ¬ 2 ∣ oddRad r := by
  unfold oddRad
  intro h2
  obtain ⟨p, hp, hd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h2
  rw [mem_filter, Nat.mem_primeFactors] at hp
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.1.1).1 hd
  omega

theorem oddRad_pos (r : ℕ) : 0 < oddRad r := by
  unfold oddRad
  exact prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).pos

theorem oddRad_dvd (r : ℕ) : oddRad r ∣ r := by
  unfold oddRad
  exact (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd r)

/-- The modulus `s = r'/(r', C*)` of p.7: odd, `r ∣ C* n ⟹ s ∣ n`, and `s C* ≥ r'`. -/
theorem sMod_spec (r Cstar : ℕ) (hC : 1 ≤ Cstar) :
    let s := oddRad r / Nat.gcd (oddRad r) Cstar
    Odd s ∧ (∀ n : ℕ, r ∣ Cstar * n → s ∣ n) ∧ (oddRad r : ℝ) ≤ s * Cstar := by
  intro s
  have hg0 : 0 < Nat.gcd (oddRad r) Cstar := Nat.gcd_pos_of_pos_left _ (oddRad_pos r)
  have hsg : s * Nat.gcd (oddRad r) Cstar = oddRad r := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  refine ⟨?_, fun n hn => ?_, ?_⟩
  · exact Odd.of_dvd_nat (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (oddRad_odd r)))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  · have h1 : oddRad r ∣ Cstar * n := (oddRad_dvd r).trans hn
    set g := Nat.gcd (oddRad r) Cstar
    have htg : Cstar / g * g = Cstar := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hcop : Nat.Coprime s (Cstar / g) := Nat.coprime_div_gcd_div_gcd hg0
    have h2 : g * s ∣ g * (Cstar / g * n) := by
      rw [mul_comm g s, hsg, ← mul_assoc, mul_comm g, htg]; exact h1
    have h3 : s ∣ Cstar / g * n := Nat.dvd_of_mul_dvd_mul_left hg0 h2
    exact hcop.dvd_of_dvd_mul_left h3
  · have hle : Nat.gcd (oddRad r) Cstar ≤ Cstar := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
    have : (oddRad r : ℝ) = s * Nat.gcd (oddRad r) Cstar := by exact_mod_cast hsg.symm
    rw [this]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- `y < 2^y` for real `y ≥ 0`. -/
theorem lt_two_rpow {y : ℝ} (hy : 0 ≤ y) : y < (2 : ℝ) ^ y := by
  have h1 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (⌊y⌋₊ : ℕ) := by
    exact_mod_cast Nat.lt_two_pow_self
  have h3 : (2 : ℝ) ^ (⌊y⌋₊ : ℕ) ≤ (2 : ℝ) ^ y := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)
  push_cast at h2
  linarith

/-- `2^{⌊L'⌋} ≤ X / 2^{√L}` once `L ≥ 1`. -/
theorem two_pow_floorLp_le {X : ℝ} (hX : 0 < X) (hL : 1 ≤ Lg X) :
    (2 : ℝ) ^ ⌊Lp X⌋₊ ≤ X / (2 : ℝ) ^ √(Lg X) := by
  have hsq : √(Lg X) ≤ Lg X := by
    calc √(Lg X) ≤ √(Lg X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = Lg X := Real.sqrt_sq (by linarith)
  have hLp : 0 ≤ Lp X := by unfold Lp; linarith
  rw [← Real.rpow_natCast]
  calc (2 : ℝ) ^ (⌊Lp X⌋₊ : ℝ) ≤ (2 : ℝ) ^ Lp X :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hLp)
    _ = X / (2 : ℝ) ^ √(Lg X) := by
        unfold Lp; rw [Real.rpow_sub (by norm_num)]; unfold Lg
        rw [Real.rpow_logb (by norm_num) (by norm_num) hX]

/-- Every `2^{ν_1} + … + 2^{ν_k} ≤ X/6` once `L ≥ 36 k²`, `k ≥ 1`. -/
theorem pow2sum_small {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 0 < X) (hL : 36 * (k : ℝ) ^ 2 ≤ Lg X)
    {ν : Fin k → ℕ} (hν : ν ∈ tuples k ⌊Lp X⌋₊) : (pow2sum ν : ℝ) ≤ X / 6 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : 1 ≤ Lg X := by nlinarith
  have h6k : 6 * (k : ℝ) ≤ √(Lg X) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; nlinarith
  have h2 : 6 * (k : ℝ) < (2 : ℝ) ^ √(Lg X) := lt_of_le_of_lt h6k (lt_two_rpow (Real.sqrt_nonneg _))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ √(Lg X) := by positivity
  calc (pow2sum ν : ℝ) ≤ k * (2 : ℝ) ^ ⌊Lp X⌋₊ := by exact_mod_cast pow2sum_le hν
    _ ≤ k * (X / (2 : ℝ) ^ √(Lg X)) :=
        mul_le_mul_of_nonneg_left (two_pow_floorLp_le hX hL1) (by linarith)
    _ ≤ X / 6 := by
        rw [mul_div_assoc', div_le_div_iff₀ hpos (by norm_num)]
        nlinarith

/-- Eventually `L ≥ L₀`. -/
theorem Lg_ge {L0 X : ℝ} (hX : (2 : ℝ) ^ L0 ≤ X) : L0 ≤ Lg X := by
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  unfold Lg
  exact (Real.le_logb_iff_rpow_le (by norm_num) hX0).2 hX

set_option maxHeartbeats 800000 in
/-- **The repaired (25), CONDITIONAL ON `Cor42W`, `Lemma62` and `R3Asymp`.** -/
theorem eq25_twoC0_of_cor42 (hC : Cor42W) (h62 : Lemma62) (h3 : R3Asymp) :
    Eq25C (fun k N => twoC0 * Ckn k N) := by
  classical
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨η0, hη0, HC⟩ := hC
  set Cm := ∑' d, romanovTerm d with hCm
  have hc0 : 0 ≤ twoC0 := twoC0_pos.le
  refine ⟨twoC0 * Cm + 3, min η0 1, lt_min hη0 one_pos, fun η hη hηlt => ?_⟩
  have hη1 : η ≤ 1 := (lt_of_lt_of_le hηlt (min_le_right _ _)).le
  obtain ⟨Cstar, C1, c, Bc, X0c, hCs, hc, HX⟩ := HC η hη (lt_of_lt_of_le hηlt (min_le_left _ _))
  set ε := η / ((|Bc| + 1) * (C1 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨r0, X62, H62⟩ := h62 ε hε0
  obtain ⟨X3, H3⟩ := h3 (j + 1) hk η hη
  set Lmin : ℝ := 36 * ((j + 1 : ℕ) : ℝ) ^ 2 + r0 * Cstar / c + 1 with hLmin
  refine ⟨max (max X0c X62) (max X3 (max 64 ((2 : ℝ) ^ Lmin))), fun X hX => ?_⟩
  have hXc : X0c ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX62 : X62 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX64 : 64 ≤ X := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hXL : (2 : ℝ) ^ Lmin ≤ X := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX0 : 0 < X := by linarith
  have hL : Lmin ≤ Lg X := Lg_ge hXL
  rw [hLmin] at hL
  have hr0c : 0 ≤ (r0 : ℝ) * Cstar / c := by positivity
  have hL36 : 36 * ((j + 1 : ℕ) : ℝ) ^ 2 ≤ Lg X := by
    have := hL; push_cast at this ⊢; linarith
  have hL1 : 1 ≤ Lg X := by linarith [sq_nonneg (((j + 1 : ℕ) : ℝ))]
  have hL0 : 0 ≤ Lg X := by linarith
  obtain ⟨P, hPR, rs, hcard, hrs, hgood, hall⟩ := HX X hXc
  obtain ⟨hP0, hPX⟩ := prange_ok hX64 hPR
  refine ⟨P, hPR, fun N hNe hNJ => ?_⟩
  set M := ⌊Lp X⌋₊ with hM
  have hNX : (N : ℝ) ≤ X := hNJ.2
  have hN23 : 2 * X / 3 ≤ N := hNJ.1
  -- the window facts
  have hsmall : ∀ ν ∈ tuples (j + 1) M, (pow2sum ν : ℝ) ≤ X / 6 :=
    fun ν hν => pow2sum_small (by omega) hX0 hL36 hν
  have hlt : ∀ ν ∈ tuples (j + 1) M, pow2sum ν < N := by
    intro ν hν
    have := hsmall ν hν
    exact_mod_cast (show (pow2sum ν : ℝ) < N by linarith)
  have hwinν : ∀ ν ∈ tuples (j + 1) M, X / 2 ≤ ((N - pow2sum ν : ℕ) : ℝ) ∧
      ((N - pow2sum ν : ℕ) : ℝ) ≤ X ∧ ((N - pow2sum ν : ℕ) : ℝ) ≤ N ∧ Even (N - pow2sum ν) := by
    intro ν hν
    have h1 := hsmall ν hν
    have h2 := hlt ν hν
    rw [Nat.cast_sub h2.le]
    refine ⟨by linarith, by linarith [(Nat.cast_nonneg (pow2sum ν) : (0 : ℝ) ≤ _)],
      by linarith [(Nat.cast_nonneg (pow2sum ν) : (0 : ℝ) ≤ _)], ?_⟩
    exact (Nat.even_sub h2.le).2 ⟨fun _ => even_pow2sum hν, fun _ => hNe⟩
  have hwint : ∀ t ∈ tuples j M, X / 2 ≤ ((N - pow2sum t : ℕ) : ℝ) := by
    intro t ht
    have hk' : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : (pow2sum t : ℝ) ≤ X / 6 := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp [pow2sum]; linarith
      · exact pow2sum_small hj hX0 (le_trans (by nlinarith) hL36) ht
    have h2 : pow2sum t ≤ N := by exact_mod_cast (show (pow2sum t : ℝ) ≤ N by linarith)
    rw [Nat.cast_sub h2]; linarith
  -- Step 1
  rw [RMpp_expand (j + 1) hP0 hPX N (fun ν hν => (hlt ν hν).le)]
  -- Step 2, (11) and (12)
  have hsplit := split_bound (j + 1) X P N Cstar rs (η := η) (abs_nonneg Bc) hη.le
    (fun ν hν hG => by
      obtain ⟨w1, w2, _, w4⟩ := hwinν ν hν
      have := hgood _ w4 w1 w2 hG
      push_cast at this ⊢; exact this)
    (fun ν hν => by
      obtain ⟨w1, w2, _, w4⟩ := hwinν ν hν
      refine (hall _ w4 w1 w2).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Nat.cast_nonneg _)) (sing_nonneg _))
  -- (14): the moduli `s(r)`
  let s : ℕ → ℕ := fun r => oddRad r / Nat.gcd (oddRad r) Cstar
  have hJ2 := J2_bound j X N Cstar rs s ε
    (fun r _ n hn => (sMod_spec r Cstar hCs).2.1 n hn)
    (fun r hr m hm1 hm2 => by
      obtain ⟨hodd, _, hsC⟩ := sMod_spec r Cstar hCs
      refine H62 X hX62 m hm1 hm2 (s r) hodd ?_
      have hCs' : (0 : ℝ) < Cstar := by exact_mod_cast hCs
      have hLsq : (r0 : ℝ) * Cstar / c ≤ Lg X ^ 2 := by nlinarith
      have h1 : (r0 : ℝ) * Cstar ≤ c * Lg X ^ 2 := by
        rw [div_le_iff₀ hc] at hLsq; linarith
      have h2 : (r0 : ℝ) * Cstar ≤ (s r : ℝ) * Cstar := le_trans h1 (le_trans (hrs r hr) hsC)
      exact_mod_cast le_of_mul_le_mul_right h2 hCs')
    hNX hlt hwint
  -- the `J₂` sum with the weight `n_ν ≤ N`
  set Q : ℝ := (N : ℝ) * Lg X ^ (j + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hbadw : ∑ ν ∈ (tuples (j + 1) M).filter (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
      ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) ≤
      N * (rs.card * (M : ℝ) ^ j * (ε * Lg X)) := by
    refine le_trans (sum_le_sum fun ν hν => mul_le_mul_of_nonneg_right
      (hwinν ν (mem_filter.1 hν).1).2.2.1 (sing_nonneg _)) ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left hJ2 (Nat.cast_nonneg _)
  have hMj : (M : ℝ) ^ j ≤ Lg X ^ j := by
    have hsq : √(Lg X) ≤ Lg X := by
      calc √(Lg X) ≤ √(Lg X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Lg X := Real.sqrt_sq hL0
    have hMp : (M : ℝ) ≤ Lp X := Nat.floor_le (by unfold Lp; linarith)
    have : Lp X ≤ Lg X := by unfold Lp; linarith [Real.sqrt_nonneg (Lg X)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hMp.trans this) j
  have hepsC : (|Bc| + 1) * rs.card * ε ≤ η := by
    have hC1 : (rs.card : ℝ) ≤ C1 := by exact_mod_cast hcard
    have hpos : 0 < (|Bc| + 1) * ((C1 : ℝ) + 1) := by positivity
    calc (|Bc| + 1) * rs.card * ε ≤ (|Bc| + 1) * C1 * ε := by gcongr
      _ = η * (C1 / (C1 + 1)) := by rw [hε]; field_simp
      _ ≤ η * 1 := by
          gcongr; rw [div_le_one (by positivity)]; linarith
      _ = η := mul_one η
  have hbad : (|Bc| + 1) * ∑ ν ∈ (tuples (j + 1) M).filter
      (fun ν => ¬ Good rs Cstar (N - pow2sum ν)),
        ((N - pow2sum ν : ℕ) : ℝ) * sing (N - pow2sum ν) ≤ η * Q := by
    refine le_trans (mul_le_mul_of_nonneg_left hbadw (by positivity)) ?_
    have hrw : (|Bc| + 1) * (N * (rs.card * (M : ℝ) ^ j * (ε * Lg X))) =
        ((|Bc| + 1) * rs.card * ε) * (N * (M : ℝ) ^ j * Lg X) := by ring
    rw [hrw, hQ, pow_succ]
    have h1 : (N : ℝ) * (M : ℝ) ^ j * Lg X ≤ N * Lg X ^ j * Lg X := by gcongr
    have h2 : 0 ≤ (N : ℝ) * (M : ℝ) ^ j * Lg X := by positivity
    calc ((|Bc| + 1) * rs.card * ε) * (N * (M : ℝ) ^ j * Lg X) ≤ η * (N * (M : ℝ) ^ j * Lg X) :=
          mul_le_mul_of_nonneg_right hepsC h2
      _ ≤ η * (N * Lg X ^ j * Lg X) := mul_le_mul_of_nonneg_left h1 hη.le
      _ = η * (N * (Lg X ^ j * Lg X)) := by ring
  -- (15) to (24)
  have hR3 := H3 X hX3 N hNe hNJ
  set T : ℝ := twoC0 * Ckn (j + 1) N * N * Lg X ^ (j + 1) with hT
  have hTle : T ≤ twoC0 * Cm * Q := by
    rw [hT, hQ, mul_assoc (twoC0 * Ckn (j + 1) N)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Corollary.Ckn_bounds j N).2 hc0) hQ0
  have hR3' : |R3 (j + 1) X N - T| ≤ η * Q := by rw [hQ, ← mul_assoc]; exact hR3
  have hR3up : R3 (j + 1) X N ≤ twoC0 * Cm * Q + η * Q := by
    have := (abs_le.1 hR3').2; linarith
  have hηR3 : η * R3 (j + 1) X N ≤ η * (twoC0 * Cm * Q) + η * Q := by
    have h1 := mul_le_mul_of_nonneg_left hR3up hη.le
    have h2 : η * (η * Q) ≤ η * Q := by
      have := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hη.le hQ0); linarith
    linarith
  -- assemble
  have hcast : (((twoC0 * Ckn (j + 1) N : ℝ) : ℂ) * (N : ℂ) * ((Lg X : ℝ) : ℂ) ^ (j + 1)) =
      ((T : ℝ) : ℂ) := by rw [hT]; push_cast; ring
  simp only at hcast ⊢
  rw [hcast]
  have htri : ‖(∑ ν ∈ tuples (j + 1) M, RM X P (N - pow2sum ν)) - ((T : ℝ) : ℂ)‖ ≤
      ‖(∑ ν ∈ tuples (j + 1) M, RM X P (N - pow2sum ν)) - ((R3 (j + 1) X N : ℝ) : ℂ)‖ +
        |R3 (j + 1) X N - T| := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ (((R3 (j + 1) X N : ℝ) : ℂ)) _).trans ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hgoal : (twoC0 * Cm + 3) * η * N * Lg X ^ (j + 1) = (twoC0 * Cm + 3) * η * Q := by
    rw [hQ]; ring
  rw [hgoal]
  have hfin : (twoC0 * Cm + 3) * η * Q = η * (twoC0 * Cm * Q) + 3 * (η * Q) := by ring
  rw [hfin]
  linarith [hsplit, htri, hbad, hηR3, hR3']

/-- **The repaired Theorem on `J(X)`**, constant `2c0 C(k, N)`, `≪ X^{3/5} (log X)^{10}`
exceptions, CONDITIONAL ON `Cor42W`, `Lemma62` and `R3Asymp`; the cited `eq25_twoC0` is not used. -/
theorem mainJ_twoC0_of_cor42 (hC : Cor42W) (h62 : Lemma62) (h3 : R3Asymp) : MainJ_twoC0 :=
  MinorBoundProof.mainJ_twoC0_of_eq25 (eq25_twoC0_of_cor42 hC h62 h3)

/-- **I-0091 at `σ = 19/24`** with the sorry `eq25_twoC0` replaced by the named inputs:
exceptions `≪ X^{7/12} (log X)^{10}`, CONDITIONAL ON `MinorBoundσ (19/24)`, `Cor42W`, `Lemma62`,
`R3Asymp`; (3) is the PROVED `eq3_proved`. -/
theorem main_19_24_of_cor42 (hm : MinorBoundσ (19 / 24)) (hC : Cor42W) (h62 : Lemma62)
    (h3 : R3Asymp) :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((ExcJC (fun k N => twoC0 * Ckn k N) k X η).card : ℝ) ≤
        B * X ^ (7 / 12 : ℝ) * Real.log X ^ 10 :=
  main_19_24 _ RgUpperProof.eq3_proved hm (eq25_twoC0_of_cor42 hC h62 h3)

/-! ### Lemma 6.2 discharged by the port `Lemma62Port.lemma62_A` -/

/-- **The repaired (25), CONDITIONAL ON `Cor42W` and `R3Asymp` only**; Lemma 6.2 is PROVED. -/
theorem eq25_twoC0_of_cor42_r3 (hC : Cor42W) (h3 : R3Asymp) :
    Eq25C (fun k N => twoC0 * Ckn k N) :=
  eq25_twoC0_of_cor42 hC Lemma62Port.lemma62_A h3

/-- **The repaired Theorem on `J(X)`, CONDITIONAL ON `Cor42W` and `R3Asymp` only.** -/
theorem mainJ_twoC0_of_cor42_r3 (hC : Cor42W) (h3 : R3Asymp) : MainJ_twoC0 :=
  mainJ_twoC0_of_cor42 hC Lemma62Port.lemma62_A h3

/-- **I-0091 at `σ = 19/24`, CONDITIONAL ON `MinorBoundσ (19/24)`, `Cor42W` and `R3Asymp` only.** -/
theorem main_19_24_of_cor42_r3 (hm : MinorBoundσ (19 / 24)) (hC : Cor42W) (h3 : R3Asymp) :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((ExcJC (fun k N => twoC0 * Ckn k N) k X η).card : ℝ) ≤
        B * X ^ (7 / 12 : ℝ) * Real.log X ^ 10 :=
  main_19_24_of_cor42 hm hC Lemma62Port.lemma62_A h3

end

end LeanLab.LPZ2007.Eq14FromCor42
