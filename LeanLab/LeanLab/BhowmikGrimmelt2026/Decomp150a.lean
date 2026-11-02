/-
Theorem 3.1, P0029 pages 9 to 13.
OPEN leaves for Jules. The assembly is CONDITIONAL on these leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-- LEAF. Page 12, the best possible zero bound is at least one half.
Cited input: existence of a nontrivial zeta zero on the critical line,
Hardy 1914, Sur les zeros de la fonction zeta de Riemann.
OPEN. This input is not proved by the survey. -/
theorem zeroBound_lower150 {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  sorry

/-- LEAF. Page 13 display 3.8, from the character zero error in 3.7 and Parseval.
OPEN. The uniform explicit formula and arc summation remain to be supplied. -/
theorem mean_square150 : MeanSquare38 := by
  sorry

/-- LEAF. Page 13, the singular series lower bound and removal of proper prime powers.
For large even exceptions the representation error has size at least a fixed multiple of N.
OPEN. The singular series lower bound is also discussed on page 6. -/
theorem exceptional_gap150 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ¬ IsGoldbachSum N → c * N ≤ |E2 N| := by
  sorry

/-- Counting lemma, the Chebyshev step of page 13 in the form the paper uses it: a second-moment
bound `∑ n² ≤ K t^{γ+2}` over a set of naturals forces the number of its elements below `t` to be
`O(t^γ)`. The proof splits the count at `t/2` and iterates that split, which is what makes the
exponent improve from `γ + 2` to `γ`. -/
private lemma card_filter_le_of_sum_sq_le {K γ : ℝ} (hK : 0 < K) (hγ : 0 < γ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, 4 ≤ n)
    (hsum : ∀ t : ℕ, 1 ≤ t →
      ∑ n ∈ T.filter (fun m => m ≤ t), (n : ℝ) ^ 2 ≤ K * (t : ℝ) ^ (γ + 2)) :
    ∀ X : ℕ, ((T.filter (fun m => m ≤ X)).card : ℝ) ≤
      4 * K / (1 - 2 ^ (-γ)) * (X : ℝ) ^ γ := by
  have h2lt : (2 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : (0 : ℝ) < 1 - 2 ^ (-γ) := by linarith
  have hcoef : (0 : ℝ) < 4 * K / (1 - 2 ^ (-γ)) := by positivity
  have key : ∀ t : ℕ, ∀ m ≤ t, ((T.filter (fun k => k ≤ m)).card : ℝ) ≤
      4 * K / (1 - 2 ^ (-γ)) * (m : ℝ) ^ γ := by
    intro t
    induction t with
    | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      have hempty : T.filter (fun k => k ≤ 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        have := hT n hn
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hcoef.le (Real.zero_rpow_nonneg γ)
    | succ t ih =>
      intro m hm
      rcases Nat.lt_or_ge m (t + 1) with hlt | hge
      · exact ih m (by omega)
      · have hm' : m = t + 1 := by omega
        subst hm'
        have hpos : 0 < t + 1 := Nat.succ_pos t
        have hdiv : (t + 1) / 2 < t + 1 := Nat.div_lt_self hpos (by norm_num)
        have hIHE := ih ((t + 1) / 2) (by omega)
        set S : Finset ℕ := T.filter (fun n => (t + 1) / 2 < n ∧ n ≤ t + 1) with hSdef
        have hsplit : T.filter (fun n => n ≤ t + 1) =
            T.filter (fun n => n ≤ (t + 1) / 2) ∪ S := by
          rw [hSdef]
          ext n
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hnT, hnt⟩
            by_cases h : n ≤ (t + 1) / 2
            · exact Or.inl ⟨hnT, h⟩
            · exact Or.inr ⟨hnT, Nat.lt_of_not_le h, hnt⟩
          · rintro (⟨hnT, h⟩ | ⟨hnT, h1, h2⟩)
            · exact ⟨hnT, le_trans h (Nat.div_le_self (t + 1) 2)⟩
            · exact ⟨hnT, h2⟩
        have hdisj : Disjoint (T.filter (fun n => n ≤ (t + 1) / 2)) S := by
          rw [Finset.disjoint_left]
          intro n hn1 hn2
          simp only [Finset.mem_filter, hSdef] at hn1 hn2
          omega
        have hcard : ((T.filter (fun n => n ≤ t + 1)).card : ℝ)
            = ((T.filter (fun n => n ≤ (t + 1) / 2)).card : ℝ) + (S.card : ℝ) := by
          rw [hsplit, Finset.card_union_of_disjoint hdisj]
          push_cast
          ring
        have hhalf : (((t + 1) / 2 : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) / 2 := by
          have h := Nat.div_mul_le_self (t + 1) 2
          have h' : (((t + 1) / 2 : ℕ) : ℝ) * 2 ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h
          linarith
        have hSge : ∀ n ∈ S, (((t + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
          intro n hn
          simp only [hSdef, Finset.mem_filter] at hn
          have hnat : t + 1 ≤ 2 * n := by omega
          have hcast2 : ((t + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
          have hle : ((t + 1 : ℕ) : ℝ) / 2 ≤ (n : ℝ) := by linarith
          have h0 : (0 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) / 2 := by positivity
          exact pow_le_pow_left₀ h0 hle 2
        have hSsum : (S.card : ℝ) * (((t + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ ∑ n ∈ S, (n : ℝ) ^ 2 := by
          have h1 := Finset.card_nsmul_le_sum S (fun n => (n : ℝ) ^ 2)
            ((((t + 1 : ℕ) : ℝ) / 2) ^ 2) hSge
          simpa [nsmul_eq_mul] using h1
        have hSle : ∑ n ∈ S, (n : ℝ) ^ 2 ≤ K * ((t + 1 : ℕ) : ℝ) ^ (γ + 2) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hsum (t + 1) (by omega))
          · intro n hn
            simp only [hSdef, Finset.mem_filter] at hn ⊢
            exact ⟨hn.1, hn.2.2⟩
          · intro n _ _
            positivity
        have hSpow : ((t + 1 : ℕ) : ℝ) ^ (γ + 2)
            = ((t + 1 : ℕ) : ℝ) ^ γ * ((t + 1 : ℕ) : ℝ) ^ 2 := by
          have ht0 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by positivity
          have h2 : ((t + 1 : ℕ) : ℝ) ^ (2 : ℝ) = ((t + 1 : ℕ) : ℝ) ^ 2 := by
            simp
          rw [Real.rpow_add ht0 γ 2, h2]
        have hcardS : (S.card : ℝ) ≤ 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := by
          rw [hSpow] at hSle
          have ht2 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) ^ 2 := by positivity
          have hR : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) ^ γ := Real.rpow_pos_of_pos (by positivity) γ
          have hsq : (((t + 1 : ℕ) : ℝ) / 2) ^ 2 = ((t + 1 : ℕ) : ℝ) ^ 2 / 4 := by ring
          rw [hsq] at hSsum
          nlinarith [hSsum, hSle, ht2, hR, hK]
        have hstep : 4 * K / (1 - 2 ^ (-γ)) * (((t + 1) / 2 : ℕ) : ℝ) ^ γ
            ≤ 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhalf hγ.le) hcoef.le
        have hfin : 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ
            = (4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ)) * ((t + 1 : ℕ) : ℝ) ^ γ := by
          have h2γ : (2 : ℝ) ^ γ ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) γ).ne'
          have hc0 : (1 : ℝ) - 2 ^ (-γ) ≠ 0 := ne_of_gt hden
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]
          field_simp
        have hconst : 4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ) + 4 * K = 4 * K / (1 - 2 ^ (-γ)) := by
          have hc0 : (1 : ℝ) - 2 ^ (-γ) ≠ 0 := ne_of_gt hden
          field_simp
          ring
        calc ((T.filter (fun n => n ≤ t + 1)).card : ℝ)
            = ((T.filter (fun n => n ≤ (t + 1) / 2)).card : ℝ) + (S.card : ℝ) := hcard
          _ ≤ 4 * K / (1 - 2 ^ (-γ)) * ((((t + 1) / 2 : ℕ)) : ℝ) ^ γ
                + 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := add_le_add hIHE hcardS
          _ ≤ 4 * K / (1 - 2 ^ (-γ)) * (((t + 1 : ℕ) : ℝ) / 2) ^ γ
                + 4 * K * ((t + 1 : ℕ) : ℝ) ^ γ := by linarith [hstep]
          _ = (4 * K / (1 - 2 ^ (-γ)) * 2 ^ (-γ) + 4 * K) * ((t + 1 : ℕ) : ℝ) ^ γ := by
              rw [hfin]; ring
          _ = 4 * K / (1 - 2 ^ (-γ)) * ((t + 1 : ℕ) : ℝ) ^ γ := by rw [hconst]
  intro X
  exact key X X le_rfl

/-- LEAF. Page 13, Chebyshev on dyadic intervals and summation over the intervals.
The restriction a greater than two makes the final exponent positive.
OPEN. Finite initial exceptions must be absorbed into the constant. -/
theorem moment_to_count150 (a : ℝ) (ha : 2 < a) (bad : ℕ → Prop)
    [DecidablePred bad] (f : ℕ → ℝ)
    (hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → bad N → c * N ≤ |f N|)
    (hmean : ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, (f N) ^ 2 ≤ C * (X : ℝ) ^ a) :
    ∃ D : ℝ, ∀ X : ℕ, 1 ≤ X →
      (((Finset.Icc 4 X).filter bad).card : ℝ) ≤ D * (X : ℝ) ^ (a - 2) := by
  obtain ⟨c, hc, N₀, hgap⟩ := hgap
  obtain ⟨C₀, hC₀⟩ := hmean
  have hCpos : (0 : ℝ) < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hγ : (0 : ℝ) < a - 2 := by linarith
  have hKpos : (0 : ℝ) < max C₀ 1 / c ^ 2 := by positivity
  have h2lt : (2 : ℝ) ^ (-(a - 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : (0 : ℝ) < 1 - 2 ^ (-(a - 2)) := by linarith
  refine ⟨((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))), ?_⟩
  intro X hX
  have hDD : (0 : ℝ) ≤ 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) :=
    div_nonneg (by positivity) hden.le
  have hM0 : (0 : ℝ) ≤ ((max 4 N₀ : ℕ) : ℝ) + 1 := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hXγ : (1 : ℝ) ≤ (X : ℝ) ^ (a - 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (a - 2) := (Real.one_rpow _).symm
      _ ≤ (X : ℝ) ^ (a - 2) := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hX) hγ.le
  have hXγpos : (0 : ℝ) < (X : ℝ) ^ (a - 2) := lt_of_lt_of_le one_pos hXγ
  -- the set of exceptions inside `[max 4 N₀, X]`, where the gap hypothesis applies
  have hT4 : ∀ n ∈ (Finset.Icc (max 4 N₀) X).filter bad, 4 ≤ n := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    omega
  have hpoint : ∀ n ∈ (Finset.Icc (max 4 N₀) X).filter bad,
      c ^ 2 * (n : ℝ) ^ 2 ≤ (f n) ^ 2 := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h4, _⟩, hb⟩ := hn
    have hN₀ : N₀ ≤ n := by omega
    have h := hgap n hN₀ hb
    have h0 : (0 : ℝ) ≤ c * n := by positivity
    calc c ^ 2 * (n : ℝ) ^ 2 = (c * n) ^ 2 := by ring
      _ ≤ |f n| ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = (f n) ^ 2 := sq_abs _
  have hsum : ∀ t : ℕ, 1 ≤ t →
      ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ (max C₀ 1 / c ^ 2) * (t : ℝ) ^ ((a - 2) + 2) := by
    intro t ht
    have hTA : ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t)
        ⊆ Finset.Icc 1 t := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    have h1 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2 / c ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hp := hpoint n (Finset.mem_of_mem_filter n hn)
      have hc2 : (0 : ℝ) < c ^ 2 := by positivity
      rw [le_div_iff₀ hc2]
      linarith [hp]
    have h2 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
          (f n) ^ 2 / c ^ 2
        = (∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (f n) ^ 2)
          / c ^ 2 := by
      rw [Finset.sum_div]
    have h3 : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (f n) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 t, (f n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hTA (fun n _ _ => by positivity)
    have h4 := hC₀ t ht
    have h5 : C₀ * (t : ℝ) ^ a ≤ max C₀ 1 * (t : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hnum : ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
        (f n) ^ 2 ≤ max C₀ 1 * (t : ℝ) ^ a := le_trans h3 (le_trans h4 h5)
    have hexp : (t : ℝ) ^ ((a - 2) + 2) = (t : ℝ) ^ a := by
      have h : (a - 2) + 2 = a := by ring
      rw [h]
    rw [hexp]
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    calc ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t), (n : ℝ) ^ 2
        ≤ ∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2 / c ^ 2 := h1
      _ = (∑ n ∈ ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ t),
            (f n) ^ 2) * (c ^ 2)⁻¹ := by rw [h2, div_eq_mul_inv]
      _ ≤ (max C₀ 1 * (t : ℝ) ^ a) * (c ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = max C₀ 1 / c ^ 2 * (t : ℝ) ^ a := by
          rw [div_eq_mul_inv]
          ring

  have hmain := card_filter_le_of_sum_sq_le hKpos hγ
    ((Finset.Icc (max 4 N₀) X).filter bad) hT4 hsum X
  have hTeq : ((Finset.Icc (max 4 N₀) X).filter bad).filter (fun m => m ≤ X)
      = (Finset.Icc (max 4 N₀) X).filter bad := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, by omega⟩
  rw [hTeq] at hmain
  -- absorb the finitely many exceptions below `max 4 N₀`
  have hsub : (Finset.Icc 4 X).filter bad
      ⊆ Finset.range (max 4 N₀ + 1) ∪ (Finset.Icc (max 4 N₀) X).filter bad := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_range] at hn ⊢
    obtain ⟨⟨h4, hX'⟩, hb⟩ := hn
    by_cases h : n ≤ max 4 N₀
    · exact Or.inl (by omega)
    · exact Or.inr ⟨⟨by omega, hX'⟩, hb⟩
  have hcard1 : ((Finset.Icc 4 X).filter bad).card
      ≤ (max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card := by
    calc ((Finset.Icc 4 X).filter bad).card
        ≤ (Finset.range (max 4 N₀ + 1) ∪ (Finset.Icc (max 4 N₀) X).filter bad).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range (max 4 N₀ + 1)).card + ((Finset.Icc (max 4 N₀) X).filter bad).card :=
          Finset.card_union_le _ _
      _ = (max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card := by
          rw [Finset.card_range]
  have hc1 : (((Finset.Icc 4 X).filter bad).card : ℝ)
      ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := by
    have h : (((max 4 N₀ + 1) + ((Finset.Icc (max 4 N₀) X).filter bad).card : ℕ) : ℝ)
        = ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := by
      push_cast
      ring
    rw [← h]
    exact_mod_cast hcard1
  calc (((Finset.Icc 4 X).filter bad).card : ℝ)
      ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + (((Finset.Icc (max 4 N₀) X).filter bad).card : ℝ) := hc1
    _ ≤ ((max 4 N₀ + 1 : ℕ) : ℝ) + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) * (X : ℝ) ^ (a - 2) := by
        linarith [hmain]
    _ ≤ (((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2)))) * (X : ℝ) ^ (a - 2) := by
        have hcast : ((max 4 N₀ + 1 : ℕ) : ℝ) = ((max 4 N₀ : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        rw [hcast]
        have hid :
            (((max 4 N₀ : ℕ) : ℝ) + 1 + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))))
                * (X : ℝ) ^ (a - 2) =
              (((max 4 N₀ : ℕ) : ℝ) + 1) * (X : ℝ) ^ (a - 2)
                + 4 * (max C₀ 1 / c ^ 2) / (1 - 2 ^ (-(a - 2))) * (X : ℝ) ^ (a - 2) := by
          ring
        have hstep : (((max 4 N₀ : ℕ) : ℝ) + 1) ≤ (((max 4 N₀ : ℕ) : ℝ) + 1) * (X : ℝ) ^ (a - 2) := by
          simpa using mul_le_mul_of_nonneg_left hXγ hM0
        rw [hid]
        linarith [hstep]

/-- Exactly the sealed Theorem31 proposition. CONDITIONAL on the four OPEN leaves. -/
theorem theorem31_decomposed150 : Theorem31 := by
  intro Θ hΘ hZ ε hε
  have hhalf := zeroBound_lower150 hZ
  have hmean := mean_square150 Θ hΘ hZ ε hε
  classical
  have hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → (Even N ∧ ¬ IsGoldbachSum N) → c * N ≤ |E2 N| := by
    obtain ⟨c, hc, N₀, h⟩ := exceptional_gap150
    exact ⟨c, hc, N₀, fun N hN hb => h N hN hb.1 hb.2⟩
  have h := moment_to_count150 (3 / 2 + 2 * Θ + ε) (by linarith)
    (fun N => Even N ∧ ¬ IsGoldbachSum N) E2 hgap hmean
  change PowerBound (3 / 2 + 2 * Θ + ε - 2) at h
  have he : (3 / 2 + 2 * Θ + ε - 2 : ℝ) = 2 * Θ - 1 / 2 + ε := by ring
  rwa [he] at h

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.zeroBound_lower150
#print axioms LeanLab.BhowmikGrimmelt2026.mean_square150
#print axioms LeanLab.BhowmikGrimmelt2026.exceptional_gap150
#print axioms LeanLab.BhowmikGrimmelt2026.moment_to_count150
#print axioms LeanLab.BhowmikGrimmelt2026.theorem31_decomposed150
