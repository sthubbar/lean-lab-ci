import LeanLab.LanguascoPintzZaccagnini2007.Tail383

/-!
Journal page 779 display 30, with an explicit constant.
Positive residuals are used in every support sum, as in display 13.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Euler weight is at most five times exp 27 times log L. -/
theorem product_weight_log383 (V : Finset ℕ) (n : ℕ → ℕ) {X L : ℝ}
    (_hX : 0 < X) (hL : 2 ≤ L) (hlog : log X = L * log 2)
    (hn : ∀ v ∈ V, n v ≠ 0) (hnX : ∀ v ∈ V, (n v : ℝ) ≤ X)
    (hcard : (V.card : ℝ) ≤ L) :
    ∑ s ∈ (opf (∏ v ∈ V, n v)).powerset,
      W s ≤ 5 * exp 27 * log L := by
  classical
  let P := ∏ v ∈ V, n v
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn
  have hPX : (P : ℝ) ≤ X ^ V.card := by
    dsimp [P]
    rw [Nat.cast_prod, ← prod_const]
    exact prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hnX
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h2 : (2 : ℝ) ^ P.primeFactors.card ≤ X ^ V.card :=
      (show (2 : ℝ) ^ P.primeFactors.card ≤ (P : ℝ) by
        exact_mod_cast LeanLab.Romanov.two_pow_card_le P hP0).trans hPX
    have h4 := log_le_log (by positivity) h2
    rw [log_pow, log_pow, hlog] at h4
    have hωL : (P.primeFactors.card : ℝ) ≤ V.card * L := by
      have hl2 := log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    nlinarith
  let Y := ⌈L ^ 2⌉₊ + 4
  have hY : 4 ≤ Y := by omega
  have hωY : P.primeFactors.card ≤ Y := by
    have : (P.primeFactors.card : ℝ) ≤ (⌈L ^ 2⌉₊ : ℕ) := hω.trans (Nat.le_ceil _)
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by exact_mod_cast this
    omega
  have hYle : (Y : ℝ) ≤ L ^ 2 + 5 := by
    dsimp [Y]
    push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  have hL3 : 8 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3
    norm_num at this
    exact this
  have hL5 : L ^ 2 + 5 ≤ L ^ 5 := by
    calc L ^ 2 + 5 ≤ L ^ 2 * 8 := by nlinarith
      _ ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left hL3 (sq_nonneg _)
      _ = L ^ 5 := by ring
  have hlogY : log (Y : ℝ) ≤ 5 * log L := by
    have := log_le_log (by positivity : (0 : ℝ) < Y) (hYle.trans hL5)
    simpa only [log_pow, Nat.cast_ofNat] using this
  calc ∑ s ∈ (opf P).powerset, W s
      ≤ exp 27 * log Y := sum_W_opf_le P Y hY hωY
    _ ≤ exp 27 * (5 * log L) := mul_le_mul_of_nonneg_left hlogY (exp_pos _).le
    _ = 5 * exp 27 * log L := by ring

/-- Journal pages 778 and 779, displays 28 and 30. Odd squarefree divisors
that occur in one of finitely many positive integers are supported on the
odd prime factors of their product. -/
theorem squarefree_support_le383 {ι : Type*} (V : Finset ι) (n : ι → ℕ) (F : Finset ℕ)
    (hF : ∀ d ∈ F, OddSqf d) (hn : ∀ v ∈ V, n v ≠ 0) :
    ∑ d ∈ F.filter (fun d => ∃ v ∈ V, d ∣ n v), fd d ≤
      ∑ t ∈ (opf (∏ v ∈ V, n v)).powerset, W t := by
  classical
  let P := ∏ v ∈ V, n v
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr hn
  have hinj : Set.InjOn Nat.primeFactors (↑(F.filter (fun d => ∃ v ∈ V, d ∣ n v))) := by
    intro a ha b hb hab
    have ha' := (hF a (mem_filter.mp ha).1).2.2
    have hb' := (hF b (mem_filter.mp hb).1).2.2
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have hsub : (F.filter (fun d => ∃ v ∈ V, d ∣ n v)).image Nat.primeFactors ⊆ (opf P).powerset := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    obtain ⟨hdF, v, hv, hdv⟩ := mem_filter.mp hd
    have ho := hF d hdF
    have hdP : d ∣ P := hdv.trans (dvd_prod_of_mem n hv)
    rw [mem_powerset]
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    have hdq := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ho.2.1) (even_iff_two_dvd.mpr hdq)
    have hq3 : 2 < q := by have := hp.two_le; omega
    exact mem_filter.mpr ⟨Nat.primeFactors_mono hdP hP0 hq, hq3⟩
  refine sum_le_sum_of_injOn Nat.primeFactors hinj hsub ?_ ?_
  · intro d hd
    exact (fd_eq (hF d (mem_filter.mp hd).1)).le
  · intro t ht _
    exact W_nonneg (fun q hq => (mem_filter.mp (mem_powerset.mp ht hq)).2)

/-- Journal page 778 display 28. A star of m is the sum of f over odd
squarefree d at most X dividing at least one positive residual m minus 2 to power a. -/
def Astar383 (X m : ℕ) : ℝ :=
  ∑ d ∈ ((Icc 1 X).filter OddSqf).filter
    (fun d => ∃ a ∈ Icc 1 ⌊Lg X - √(Lg X)⌋₊, 2 ^ a < m ∧ d ∣ m - 2 ^ a), fd d

/-- Journal page 779 display 30. The support weight A star is at most
five times exp 27 times log L for m at most X and L at least 2. -/
theorem Astar_bound383 {X m : ℕ} (hL : 2 ≤ Lg X) (hm : m ≤ X) :
    Astar383 X m ≤ 5 * exp 27 * log (Lg X) := by
  classical
  let M := ⌊Lg X - √(Lg X)⌋₊
  let V := (Icc 1 M).filter (fun a => 2 ^ a < m)
  let F := (Icc 1 X).filter OddSqf
  have hF : ∀ d ∈ F, OddSqf d := fun d hd => (mem_filter.mp hd).2
  have hn : ∀ a ∈ V, m - 2 ^ a ≠ 0 := by
    intro a ha
    have := (mem_filter.mp ha).2
    omega
  have hnatX : ∀ a ∈ V, ((m - 2 ^ a : ℕ) : ℝ) ≤ X := by
    intro a _
    exact_mod_cast (Nat.sub_le m _).trans hm
  have hM : (M : ℝ) ≤ Lg X := by
    have hs : √(Lg X) ≤ Lg X := (sqrt_le_left (by linarith)).mpr (by nlinarith)
    have hf : (M : ℝ) ≤ Lg X - √(Lg X) := Nat.floor_le (by linarith)
    linarith [sqrt_nonneg (Lg X)]
  have hcard : (V.card : ℝ) ≤ Lg X := by
    have hle : V.card ≤ M := (card_filter_le _ _).trans (by simp)
    exact (show (V.card : ℝ) ≤ M by exact_mod_cast hle).trans hM
  have hXpos : 0 < (X : ℝ) := by
    by_contra hx
    have hx0 : X = 0 := by exact_mod_cast (le_antisymm (not_lt.mp hx) (Nat.cast_nonneg X))
    subst hx0
    norm_num [Lg] at hL
  have hlog : log (X : ℝ) = Lg X * log 2 := by unfold Lg Real.logb; field_simp
  have he : Astar383 X m = ∑ d ∈ F.filter (fun d => ∃ a ∈ V, d ∣ m - 2 ^ a), fd d := by
    unfold Astar383
    congr 1
    apply filter_congr
    intro d _
    simp only [V, mem_filter]
    aesop
  rw [he]
  exact (squarefree_support_le383 V (fun a => m - 2 ^ a) F hF hn).trans
    (product_weight_log383 V (fun a => m - 2 ^ a) hXpos hL hlog hn hnatX hcard)

/-- Journal page 778 display 28. A prime is the maximum of A star over m at most X. -/
def Aprime383 (X : ℕ) : ℝ :=
  (range (X + 1)).sup' (by simp : (range (X + 1)).Nonempty) (Astar383 X)

/-- Journal pages 777 and 779, displays 20 and 30. The maximum support error
is uniformly at most five times exp 27 times log L. -/
theorem Aprime_bound383 {X : ℕ} (hL : 2 ≤ Lg X) :
    Aprime383 X ≤ 5 * exp 27 * log (Lg X) := by
  apply Finset.sup'_le
  intro m hm
  exact Astar_bound383 hL (by have := mem_range.mp hm; omega)

/-- Journal page 778 display 28. The support weight is always nonnegative. -/
theorem Astar_nonneg383 (X m : ℕ) : 0 ≤ Astar383 X m := by
  exact sum_nonneg fun d hd => fd_nonneg (mem_filter.mp (mem_filter.mp hd).1).2

/-- Journal page 778 display 28 at m equal to zero. No positive residual occurs. -/
theorem Astar_zero383 (X : ℕ) : Astar383 X 0 = 0 := by
  simp [Astar383]


end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.product_weight_log383

#print axioms LeanLab.LPZ2007.squarefree_support_le383
#print axioms LeanLab.LPZ2007.Astar_bound383
#print axioms LeanLab.LPZ2007.Aprime_bound383
#print axioms LeanLab.LPZ2007.Astar_nonneg383
#print axioms LeanLab.LPZ2007.Astar_zero383
