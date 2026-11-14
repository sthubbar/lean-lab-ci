import LeanLab.ExceptionalSet.UpJ200.Decomp371a

/-!
P0082 page362 Lemma7 and page367 displays29 and30.
Source: https://doi.org/10.5802/aif.1621
The even lower bound and the two odd moments are separate OPEN inputs.
The elementary assembly remains CONDITIONAL ON these inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp505a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 page362 before Lemma6. The even member of the adjacent pair. -/
noncomputable def evenIndex (γ : ℝ) (n : ℕ) : ℤ :=
  if Even (nu γ n) then nu γ n else nu γ n + 1

/-- P0082 page362 first sentence of the Lemma7 proof.
The even and odd members give the original adjacent sum. -/
theorem adjacent_sum (f : ℤ → ℂ) (γ : ℝ) (n : ℕ) :
    f (evenIndex γ n) + f (nuOdd γ n) = f (nu γ n) + f (nu γ n + 1) := by
  by_cases he : Even (nu γ n)
  · have ho : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr he
    simp [evenIndex, nuOdd, he, ho]
  · have ho : Odd (nu γ n) := Int.not_even_iff_odd.mp he
    simp [evenIndex, nuOdd, he, ho, add_comm]

/-- P0082 page362 Lemma7 bookkeeping.
A small pair forces a small even part or a large odd norm. -/
theorem bad_pair_count {ι : Type*} (s : Finset ι) (f g : ι → ℂ) (T : ℝ) :
    (s.filter (fun n => (f n + g n).re < T)).card ≤
      (s.filter (fun n => (f n).re < 2 * T)).card +
        (s.filter (fun n => T < ‖g n‖)).card := by
  classical
  have hsub : s.filter (fun n => (f n + g n).re < T) ⊆
      s.filter (fun n => (f n).re < 2 * T) ∪ s.filter (fun n => T < ‖g n‖) := by
    intro n hn
    simp only [mem_filter, mem_union] at hn ⊢
    by_cases hf : (f n).re < 2 * T
    · exact Or.inl ⟨hn.1, hf⟩
    · right
      refine ⟨hn.1, ?_⟩
      have hr := (abs_le.mp (Complex.abs_re_le_norm (g n))).1
      simp only [Complex.add_re] at hn
      by_contra hg
      have hff := le_of_not_gt hf
      have hgg := le_of_not_gt hg
      linarith
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- P0082 page367 after displays29 and30. The finite second moment
bounds the number of odd coefficients above any positive threshold. -/
theorem norm_bad_count {ι : Type*} (s : Finset ι) (f : ι → ℂ) (T A : ℝ)
    (hT : 0 < T) (hm : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ A) :
    ((s.filter (fun n => T < ‖f n‖)).card : ℝ) * T ^ 2 ≤ A := by
  classical
  calc
    _ = ∑ _n ∈ s.filter (fun n => T < ‖f n‖), T ^ 2 := by simp
    _ ≤ ∑ n ∈ s.filter (fun n => T < ‖f n‖), ‖f n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ hT.le (Finset.mem_filter.mp hn).2.le 2
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ ≤ A := hm

/-- P0082 page362 Lemma7 using the page367 odd moment.
The sharper finite count constant is four because no tail approximation is used. -/
theorem odd_bad_count (s : Finset ℕ) (f : ℕ → ℂ)
    (c B X E : ℝ) (N : ℕ) (hc : 0 < c) (hB : 0 ≤ B) (hX : 0 < X) (hE : 1 ≤ E)
    (hm : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) :
    ((s.filter (fun n => c / 2 * X * E ^ (-(1 / 10 : ℝ)) < ‖f n‖)).card : ℝ) ≤
      (4 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ)) := by
  classical
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let T := c / 2 * X * E ^ (-(1 / 10 : ℝ))
  have hT : 0 < T := by dsimp [T]; positivity
  have hh := norm_bad_count s f T
    (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) hT hm
  have hp : E ^ (-(1 / 3 : ℝ)) ≤
      E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE0.le, ← Real.rpow_add hE0]
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hf : B * (N : ℝ) * X ^ 2 * E ^ (-(1 / 3 : ℝ)) ≤
      ((4 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ))) * T ^ 2 := by
    calc
      _ ≤ B * N * X ^ 2 * (E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        dsimp [T]
        field_simp [hc.ne']
        ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hT)).mp (hh.trans hf)

/-- P0082 page367 displays29 and30, derived statement audit.
A small moment about zero does not give a small moment about X divided by two.
The two moment bounds must together pay for the full size of the index set. -/
theorem norm_centered_obstruction {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (X A B : ℝ) (hnorm : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ A)
    (hcentered : (∑ n ∈ s, (X / 2 - (f n).re) ^ 2) ≤ B) :
    (s.card : ℝ) * X ^ 2 ≤ 8 * (A + B) := by
  have hp (n : ι) : X ^ 2 ≤ 8 * (‖f n‖ ^ 2 + (X / 2 - (f n).re) ^ 2) := by
    have hr : (f n).re ^ 2 ≤ ‖f n‖ ^ 2 := by
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg (f n).re) (Complex.abs_re_le_norm (f n)) 2
    nlinarith [sq_nonneg (X - 4 * (f n).re)]
  calc
    _ = ∑ _n ∈ s, X ^ 2 := by simp
    _ ≤ ∑ n ∈ s, 8 * (‖f n‖ ^ 2 + (X / 2 - (f n).re) ^ 2) :=
      sum_le_sum (fun n _ => hp n)
    _ = 8 * ((∑ n ∈ s, ‖f n‖ ^ 2) +
        ∑ n ∈ s, (X / 2 - (f n).re) ^ 2) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ 8 * (A + B) := by linarith

/-- P0082 page367 displays29 and30, concrete logical counterexample.
The zero odd coefficient has zero moment about zero and nonzero centered moment.
This audits a proposed inference and asserts no error in the paper. -/
theorem zero_moment_not_centered :
    (∑ n ∈ ({0} : Finset ℕ), ‖(fun _ : ℕ => (0 : ℂ)) n‖ ^ 2) = 0 ∧
      ¬ (∑ _n ∈ ({0} : Finset ℕ), ((1 : ℝ) / 2 - ((0 : ℂ)).re) ^ 2) ≤ 1 / 16 := by
  norm_num

/-- LEAF: P0082 pages362 to364 Lemma7, its even coefficient cases.
Only the even member is bounded below. The odd member and its moment are absent.
The literal floor window is the page365 range, contained in the page362 range
for large N by the existing growth audit. -/
theorem leaf_even_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenIndex γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- LEAF: P0082 page367 display29 and page366 display28.
On the even floor parity the successor coefficient is odd.
Its second moment about zero is bounded on the full half interval. -/
theorem leaf_even_parity_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF: P0082 page367 display30 and page366 display28.
On the odd floor parity the floor coefficient itself is odd.
The reflected kernel supplies its second moment about zero. -/
theorem leaf_odd_parity_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- P0082 page367 after displays29 and30.
The odd moment on the floor window is CONDITIONAL ON the two parity leaves. -/
theorem odd_moment_uniform (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N,
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := leaf_even_parity_moment γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_parity_moment γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ba + Bb, add_pos hBa hBb, max 16 (max Na Nb), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let s := Finset.Ioc (N / 2) N
  let f := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  have hsub : window γ N ⊆ s :=
    UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN16
  calc
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = (∑ n ∈ s.filter (fun n => Even (nu γ n)), ‖f n‖ ^ 2) +
        ∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)), ‖f n‖ ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not s (fun n => Even (nu γ n)) _).symm
    _ ≤ Ba * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
        Bb * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · convert ha N hNa using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        have hnO : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr hnE
        simp [f, nuOdd, hnO]
      · convert hb N hNb using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnO : Odd (nu γ n) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2
        simp [f, nuOdd, hnO]
    _ = _ := by ring

/-- P0082 page362 Lemma7. The exact target follows from the even lower
bound and the odd second moment. CONDITIONAL ON all three analytic leaves. -/
theorem coefficient_lower_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := leaf_even_lower γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := odd_moment_uniform γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, Be, hc, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bo, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c / 2, Be + 4 * Bo / c ^ 2, by positivity, by positivity,
    max 2 (max Ne No), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNo : No ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  let f : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (evenIndex γ n)
  let g : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  let T := c / 2 * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  have hpair := bad_pair_count (window γ N) f g T
  have hrewrite (n : ℕ) : f n + g n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) :=
    adjacent_sum (R1 (F γ N ^ (6 * δ)) (F γ N)) γ n
  have htwo : 2 * T = c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    ring
  simp_rw [hrewrite, htwo] at hpair
  have hodd := odd_bad_count (window γ N) g c Bo (F γ N) (calE γ κ N) N
    hc hBo.le (Real.exp_pos _) hE (ho N hNo)
  have hpairR := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hpairR
  change _ ≤ _ at hodd
  have heN := he N hNe
  change (((window γ N).filter (fun n => (f n).re <
    c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤ _ at heN
  dsimp only [T] at hpairR
  refine hpairR.trans ((add_le_add heN hodd).trans ?_)
  ring_nf
  exact le_rfl


end LeanLab.ExceptionalSet.UpJ200.Decomp505a
