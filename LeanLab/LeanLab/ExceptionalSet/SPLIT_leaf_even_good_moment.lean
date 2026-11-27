/-
Split of `leaf_even_good_moment` of `Feed1122LeafEvenMoment`, P0082, Brudern and Perelli 1998,
displays 31, 32 and 35 to 39 on pages 367 to 369, onto the paper's cited Lemmas 4, 9 and 10.

The analytic route of displays 29 to 39, Lemma 1 with the kernels of display 31, the tail cut
of display 35, the opened square of display 37 and the two ranges of display 38 and 39, is
already formalized in `Prep1122MainWire.parity_moment_of_inputs`, CONDITIONAL ON `Lemma4`,
`Lemma9` and `Lemma10`. With `j = 0` it bounds the sum of `‖R₁(ν_n + 1)‖²` over the
`n ∈ (N/2, N]` with `ν_n` even. The target sums over a filter of `Icc ((N+1)/2) N`, which for
even `N` holds the one extra index `N/2`; that term is bounded by the trivial bound
`|R₁(m)| ≤ 2 X log X` and absorbed with `(log X)² ≤ ℰ^(1/12)` and `ℰ^(1/2) ≤ N`.

* `leaf_even_good_moment_of_inputs`: the target, CONDITIONAL ON Lemmas 4, 9 and 10, no sorry.
  Its axioms also show the existing MEDIUM leaf `leaf_R1_le_sum_log_sq` of
  `Feed1122LeafR1TrivialBound`, through `leaf_R1_trivial_bound`.
* `leaf_even_good_moment_split`: the target statement verbatim, from the sealed statements
  `U1539.lemma4`, `U1539.lemma9` and `U1539.lemma10` of `State1539`. No new sorry; it inherits
  the open status of those three cited lemmas.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Feed1122LeafEvenMoment
import LeanLab.ExceptionalSet.Prep1122MainWire

namespace LeanLab.ExceptionalSet.U1539.SplitEvenGood

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE R1 Lemma4 Lemma9 Lemma10)

/-- `ℰ^(1/2) ≤ N` for large `N`, since `3 - 2γ < 1`. -/
theorem calE_half_le_N (γ κ : ℝ) (h1 : 1 < γ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → calE γ κ N ^ (1 / 2 : ℝ) ≤ N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => Real.log N ^ ((3 - 2 * γ) - 1)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < -((3 - 2 * γ) - 1))).comp hlog |>.congr
      (fun N => by simp)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hz.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 / κ)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop 1)
  refine ⟨max N₁ (max N₂ 1), fun N hN => ?_⟩
  have hL1 : 1 ≤ Real.log N := hN₂ N (by omega)
  have hLpos : 0 < Real.log N := by linarith
  have hsmall := hN₁ N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [calE, ← Real.exp_mul]
  have hsplit : Real.log N ^ (3 - 2 * γ) = Real.log N ^ ((3 - 2 * γ) - 1) * Real.log N := by
    rw [Real.rpow_sub_one hLpos.ne']
    field_simp
  calc Real.exp (κ * Real.log N ^ (3 - 2 * γ) * (1 / 2))
      ≤ Real.exp (Real.log N) := by
        apply Real.exp_le_exp.mpr
        rw [hsplit]
        have : κ * Real.log N ^ ((3 - 2 * γ) - 1) < 2 := by
          rw [lt_div_iff₀ hκ] at hsmall; linarith
        nlinarith
    _ = N := Real.exp_log hN0

/-- The target, CONDITIONAL ON Lemmas 4, 9 and 10 of P0082. -/
theorem leaf_even_good_moment_of_inputs (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n))).filter
              (fun n : ℕ => ¬ (Int.fract (F γ n) <
                  calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
                1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
                  Int.fract (F γ n))),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ :=
    LeanLab.ExceptionalSet.Prep1122MainWire.parity_moment_of_inputs h4 h9 h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₁, hm⟩ := hm κ hκ hκs
  obtain ⟨N₂, hl⟩ :=
    LeanLab.ExceptionalSet.UpJ200.Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  obtain ⟨N₃, hh⟩ := calE_half_le_N γ κ h1 hκ
  refine ⟨B + 4, by linarith, max N₁ (max N₂ (max N₃ 3)), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : 3 ≤ N := by omega
  set X := F γ N with hX
  set E := calE γ κ N with hE
  set f : ℕ → ℝ := fun n => ‖R1 (X ^ (6 * δ)) X (nu γ n + 1)‖ ^ 2 with hf
  have he := hm N hN1 0 (Or.inl rfl)
  simp only [add_zero, sub_zero] at he
  set s := (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)) with hs
  set a := (N + 1) / 2
  have hsub : ((Finset.Icc a N).filter (fun n : ℕ => Even (nu γ n))).filter
      (fun n : ℕ => ¬ (Int.fract (F γ n) < E ^ (-(1 / 3 : ℝ)) / Real.log X ^ 2 / 2 ∨
        1 - E ^ (-(1 / 3 : ℝ)) / Real.log X ^ 2 / 2 < Int.fract (F γ n))) ⊆ insert a s := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases eq_or_ne n a with h | h
    · exact h ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      simp only [hs, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, hn.1.1.2⟩, hn.1.2⟩
      have : a < n := lt_of_le_of_ne hn.1.1.1 (Ne.symm h)
      omega
  have hins : (∑ n ∈ insert a s, f n) ≤ f a + ∑ n ∈ s, f n := by
    by_cases ha : a ∈ s
    · rw [Finset.insert_eq_of_mem ha]
      have : 0 ≤ f a := sq_nonneg _
      linarith
    · rw [Finset.sum_insert ha]
  obtain ⟨hX2, hL1⟩ := LeanLab.ExceptionalSet.U1539.F_ge_two_and_log γ h1 N hN4
  have hXpos : 0 < X := by linarith
  have hE0 : 0 < E := Real.exp_pos _
  have hfa : f a ≤ 4 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
    have hb := LeanLab.ExceptionalSet.U1539.leaf_R1_trivial_bound (X ^ (6 * δ)) X hX2
      (nu γ a + 1)
    have hb2 : f a ≤ (2 * X * Real.log X) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hlog2 : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ) := hl N hN2
    have hhalf : E ^ (1 / 2 : ℝ) ≤ N := hh N hN3
    have hE1 : 1 ≤ E := by
      rw [hE, calE]; exact Real.one_le_exp (by positivity)
    have hEm : 0 < E ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hE0 _
    have hkey : E ^ (1 / 12 : ℝ) ≤ N * E ^ (-(1 / 3 : ℝ)) := by
      have h1' : E ^ (1 / 12 : ℝ) = E ^ (5 / 12 : ℝ) * E ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_add hE0]; norm_num
      have h2' : E ^ (5 / 12 : ℝ) ≤ E ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
      rw [h1']
      exact mul_le_mul_of_nonneg_right (h2'.trans hhalf) hEm.le
    calc f a ≤ (2 * X * Real.log X) ^ 2 := hb2
      _ = 4 * X ^ 2 * Real.log X ^ 2 := by ring
      _ ≤ 4 * X ^ 2 * E ^ (1 / 12 : ℝ) := by gcongr
      _ ≤ 4 * X ^ 2 * (N * E ^ (-(1 / 3 : ℝ))) := by gcongr
      _ = 4 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by ring
  calc _ ≤ ∑ n ∈ insert a s, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ f a + ∑ n ∈ s, f n := hins
    _ ≤ 4 * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) + B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) :=
        add_le_add hfa he
    _ = (B + 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by ring

/-- `leaf_even_good_moment` of `Feed1122LeafEvenMoment`, statement verbatim, from the sealed
cited statements `lemma4`, `lemma9` and `lemma10` of `State1539`. -/
theorem leaf_even_good_moment_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ ((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n))).filter
              (fun n : ℕ => ¬ (Int.fract (F γ n) <
                  calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 ∨
                1 - calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 / 2 <
                  Int.fract (F γ n))),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
  leaf_even_good_moment_of_inputs LeanLab.ExceptionalSet.U1539.lemma4
    LeanLab.ExceptionalSet.U1539.lemma9 LeanLab.ExceptionalSet.U1539.lemma10 γ h1 h2

/-- The two statements have the same type as the unit's leaf. -/
example : type_of% @leaf_even_good_moment_split =
    type_of% @LeanLab.ExceptionalSet.U1539.leaf_even_good_moment := rfl

end LeanLab.ExceptionalSet.U1539.SplitEvenGood

#print axioms LeanLab.ExceptionalSet.U1539.SplitEvenGood.calE_half_le_N
#print axioms LeanLab.ExceptionalSet.U1539.SplitEvenGood.leaf_even_good_moment_of_inputs
#print axioms LeanLab.ExceptionalSet.U1539.SplitEvenGood.leaf_even_good_moment_split
