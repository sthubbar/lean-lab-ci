/-
Jia 1996 page 260 Lemma 19, uniform form, feeding Feed578bBlocks.lemma19_blocks_uniform.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565d
import LeanLab.Languasco2004.Decomp316d

namespace LeanLab.Languasco2004.Feed578bBlocks19
open Finset Real Filter Decomp279a Decomp316a Source565 Decomp565d Decomp316d
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 260 Lemma 19 with implicit constants depending only on epsilon and B, HARD.
For one fixed N at least N₀, the constants C, D and N₀ are chosen before the dyadic scale M
and the weight a, so the bound is uniform in M and in the weights. The hypotheses are those
of page 260: Y to 119 over 135 at most M at most Y to 1 minus delta, weights in 0 to 1,
vanishing on integers with a prime factor below Y to delta. The proof on page 260 uses
Lemmas 5 and 18, whose implied constants depend only on epsilon and B. -/
theorem lemma19_uniform :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (M : ℝ) (a : ℕ → ℝ),
      (localization N ε) ^ (119 / 135 : ℝ) ≤ M →
      M ≤ (localization N ε) ^ (1 - delta ε) →
      (∀ m : ℕ, 0 ≤ a m ∧ a m ≤ 1) →
      (∀ m p : ℕ, p.Prime → p ∣ m → (p : ℝ) < (localization N ε) ^ delta ε → a m = 0) →
      (((window N ε).filter (fun n =>
        D * (singular n * weightedCofactors true N (localization N ε) M n a /
            log N ^ (2 : ℕ) + localization N ε / log N ^ B) <
          |weightedCofactors false N (localization N ε) M n a -
            singular n / log N * weightedCofactors true N (localization N ε) M n a|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by sorry

/-- Page 260 Lemma 19 union step: an exceptional set for a sum over blocks lies in the
union of the per block exceptional sets together with the set where the summed allowances
already exceed the threshold. -/
theorem sum_exceptional_subset (s : Finset ℕ) (J : Finset ℕ) (e t : ℕ → ℕ → ℝ) (θ : ℕ → ℝ) :
    s.filter (fun n => θ n < ∑ j ∈ J, e j n) ⊆
      (J.biUnion fun j => s.filter (fun n => t j n < e j n)) ∪
        s.filter (fun n => θ n < ∑ j ∈ J, t j n) := by
  intro n hn
  obtain ⟨hs, hθ⟩ := mem_filter.mp hn
  by_cases h : ∀ j ∈ J, e j n ≤ t j n
  · exact mem_union_right _ (mem_filter.mpr ⟨hs, lt_of_lt_of_le hθ (sum_le_sum h)⟩)
  · push_neg at h
    obtain ⟨j, hj, hlt⟩ := h
    exact mem_union_left _ (mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨hs, hlt⟩⟩)

/-- Page 260 Lemma 19 union step, counted: the cardinality bound behind the dyadic union. -/
theorem sum_exceptional_card (s : Finset ℕ) (J : Finset ℕ) (e t : ℕ → ℕ → ℝ) (θ : ℕ → ℝ) :
    ((s.filter (fun n => θ n < ∑ j ∈ J, e j n)).card : ℝ) ≤
      ∑ j ∈ J, ((s.filter (fun n => t j n < e j n)).card : ℝ) +
        ((s.filter (fun n => θ n < ∑ j ∈ J, t j n)).card : ℝ) := by
  have h1 := card_le_card (sum_exceptional_subset s J e t θ)
  have h2 := card_union_le (J.biUnion fun j => s.filter (fun n => t j n < e j n))
    (s.filter (fun n => θ n < ∑ j ∈ J, t j n))
  have h3 := card_biUnion_le (s := J) (t := fun j => s.filter (fun n => t j n < e j n))
  have : (s.filter (fun n => θ n < ∑ j ∈ J, e j n)).card ≤
      ∑ j ∈ J, (s.filter (fun n => t j n < e j n)).card +
        (s.filter (fun n => θ n < ∑ j ∈ J, t j n)).card := by omega
  exact_mod_cast this

/-- Page 283 support: the number of blocks is at most a fixed multiple of log N. -/
theorem ceil_blocks_le19 (K L : ℝ) (hL : 1 ≤ L) :
    ((⌈K * L⌉₊ : ℕ) : ℝ) ≤ (|K| + 1) * L := by
  have hL0 : 0 ≤ L := by linarith
  have h1 : ((⌈K * L⌉₊ : ℕ) : ℝ) ≤ ((⌈|K| * L⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self K) hL0)
  have h2 : ((⌈|K| * L⌉₊ : ℕ) : ℝ) < |K| * L + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg K) hL0)
  nlinarith [abs_nonneg K]

/-- Jia page 260 Lemma 19 summed over the dyadic blocks used in displays 59 and 63:
the exact type of `Feed578bBlocks.lemma19_blocks_uniform`, by a union bound at exponent B plus 3,
`tailProduct_le_singular` and log Y at most log N. CONDITIONAL ON the LEAF `lemma19_uniform`. -/
theorem lemma19_blocks_uniform_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ (K K₂ : ℝ) (M : ℕ → ℝ → ℝ) (w : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (119 / 135 : ℝ) ≤ M j N ∧
          M j N ≤ (localization N ε) ^ (1 - delta ε)) →
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, 0 ≤ w j N m ∧ w j N m ≤ 1) →
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → ∀ m p : ℕ, p.Prime → p ∣ m →
        (p : ℝ) < (localization N ε) ^ delta ε → w j N m = 0) →
      (∃ T : ℝ, ∀ N : ℝ, T ≤ N → ∀ n ∈ window N ε,
        ∑ j ∈ range ⌈K * log N⌉₊,
          weightedCofactors true N (localization N ε) (M j N) n (w j N) ≤
        K₂ * localization N ε / log (localization N ε)) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000001 * scale N (localization N ε) n <
          ∑ j ∈ range ⌈K * log N⌉₊,
            |weightedCofactors false N (localization N ε) (M j N) n (w j N) -
              singular n / log N *
                weightedCofactors true N (localization N ε) (M j N) n (w j N)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e, he, hL19⟩ := Feed578bBlocks19.lemma19_uniform
  refine ⟨min e (1 / 12), lt_min he (by norm_num), ?_⟩
  intro ε B hε hεe hB K K₂ M w hM hw hwp hT
  have hεe1 : ε < e := hεe.trans_le (min_le_left _ _)
  have hε12 : ε < 1 / 12 := hεe.trans_le (min_le_right _ _)
  obtain ⟨T, hTW⟩ := hT
  obtain ⟨C, D, N₀, hD, hC⟩ := hL19 ε (B + 3) hε hεe1 (by linarith)
  set c : ℝ := (|K| + 1) * D / (0.000000005 * tailProduct) with hc
  set c₁ : ℝ := D * |K₂| / 0.000000005 with hc₁
  have htend : Tendsto (fun N : ℝ => log N ^ B) atTop atTop :=
    (tendsto_rpow_atTop hB).comp tendsto_log_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htend.eventually_ge_atTop c)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (tendsto_log_atTop.eventually_ge_atTop c₁)
  refine ⟨(|K| + 1) * |C|, max (max (max N₀ N₁) (max N₂ T)) 3, ?_⟩
  intro N hN
  have hN' := (le_max_left _ _).trans hN
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN')
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN')
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN')
  have hNT : T ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN')
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log N := by
    rw [Real.le_log_iff_exp_le hNp]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hN3
  have hL : 0 < log N := by linarith
  have hc₁L : c₁ ≤ log N := hN₂ N hN2
  have hcL : c ≤ log N ^ B := hN₁ N hN1
  have hWN := hTW N hNT
  set L := log N with hLdef
  set Y := localization N ε with hYdef
  set A := windowLength N ε with hAdef
  have hYp : 1 < Y := Real.one_lt_rpow (by linarith) (by positivity : (0 : ℝ) < 7 / 12 + ε)
  have hA : 0 ≤ A := Real.rpow_nonneg hNp.le _
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL _
  have hLB3 : L ^ (B + 3) = L ^ B * L ^ 3 := by
    rw [Real.rpow_add hL]; norm_cast
  set k : ℕ := ⌈K * L⌉₊ with hk
  have hkL : (k : ℝ) ≤ (|K| + 1) * L := ceil_blocks_le19 K L hL1
  have htP := tailProduct_pos
  have hLY : 0 < log Y := Real.log_pos hYp
  have hlogY : log Y ≤ L := by
    rw [hYdef, localization, Real.log_rpow hNp]
    nlinarith
  -- per block thresholds
  set t : ℕ → ℕ → ℝ := fun j n =>
    D * (singular n * weightedCofactors true N Y (M j N) n (w j N) / L ^ (2 : ℕ) +
      Y / L ^ (B + 3)) with ht
  set ee : ℕ → ℕ → ℝ := fun j n =>
    |weightedCofactors false N Y (M j N) n (w j N) -
      singular n / L * weightedCofactors true N Y (M j N) n (w j N)| with hee
  -- the summed thresholds lie below the scale
  have hsum_small : ∀ n ∈ window N ε, ∑ j ∈ range k, t j n ≤ 0.00000001 * scale N Y n := by
    intro n hn
    have hev : Even n := (mem_filter.mp hn).2
    set S := singular n with hSdef
    have hS : tailProduct ≤ S := tailProduct_le_singular n hev
    have hS0 : 0 ≤ S := htP.le.trans hS
    set W := ∑ j ∈ range k, weightedCofactors true N Y (M j N) n (w j N) with hWdef
    have hW : W ≤ K₂ * Y / log Y := hWN n hn
    have hsplit : ∑ j ∈ range k, t j n = D * (S * W / L ^ (2 : ℕ)) + k * (D * (Y / L ^ (B + 3))) := by
      have hj : ∀ j ∈ range k, t j n = D * S / L ^ (2 : ℕ) *
          weightedCofactors true N Y (M j N) n (w j N) + D * (Y / L ^ (B + 3)) := by
        intro j _
        simp only [ht, hSdef]
        ring
      rw [hWdef, Finset.sum_congr rfl hj, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, card_range, nsmul_eq_mul]
      ring
    rw [hsplit]
    have hscale : scale N Y n = S * Y / (log Y * L) := rfl
    have hq0 : 0 ≤ S * Y / (log Y * L) := by positivity
    -- first part
    have hpart1 : D * (S * W / L ^ (2 : ℕ)) ≤ 0.000000005 * scale N Y n := by
      have hW' : W ≤ |K₂| * Y / log Y := hW.trans (by
        apply div_le_div_of_nonneg_right _ hLY.le
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
      have h1 : S * W / L ^ (2 : ℕ) ≤ |K₂| * (S * Y / (log Y * L)) / L := by
        have : S * W ≤ S * (|K₂| * Y / log Y) := mul_le_mul_of_nonneg_left hW' hS0
        calc S * W / L ^ (2 : ℕ) ≤ S * (|K₂| * Y / log Y) / L ^ (2 : ℕ) :=
              div_le_div_of_nonneg_right this (by positivity)
          _ = |K₂| * (S * Y / (log Y * L)) / L := by field_simp
      have hDK : D * |K₂| ≤ 0.000000005 * L := by
        have h := mul_le_mul_of_nonneg_left hc₁L (by norm_num : (0 : ℝ) ≤ 0.000000005)
        rw [hc₁, mul_div_cancel₀ _ (by norm_num)] at h
        exact h
      rw [hscale]
      calc D * (S * W / L ^ (2 : ℕ)) ≤ D * (|K₂| * (S * Y / (log Y * L)) / L) :=
            mul_le_mul_of_nonneg_left h1 hD.le
        _ = (D * |K₂|) * (S * Y / (log Y * L)) / L := by ring
        _ ≤ (0.000000005 * L) * (S * Y / (log Y * L)) / L :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hq0) hL.le
        _ = 0.000000005 * (S * Y / (log Y * L)) := by field_simp
    -- second part
    have hpart2 : (k : ℝ) * (D * (Y / L ^ (B + 3))) ≤ 0.000000005 * scale N Y n := by
      have hscalep := scale_pos (N := N) (Y := Y) n hev (by linarith) hYp
      have hmain : tailProduct * Y ≤ scale N Y n * L ^ 2 := by
        calc tailProduct * Y ≤ singular n * Y :=
               mul_le_mul_of_nonneg_right hS (by linarith)
             _ = scale N Y n * (log Y * L) := by
               unfold scale
               rw [div_mul_cancel₀ _ (mul_ne_zero hLY.ne' hL.ne')]
             _ ≤ scale N Y n * L ^ 2 :=
               mul_le_mul_of_nonneg_left (by nlinarith) hscalep.le
      have hcL' : (|K| + 1) * D ≤ 0.000000005 * tailProduct * L ^ B := by
        have h := mul_le_mul_of_nonneg_left hcL
          (by positivity : (0 : ℝ) ≤ 0.000000005 * tailProduct)
        rw [hc, mul_div_cancel₀ _ (by positivity)] at h
        exact h
      have hY0 : 0 ≤ Y := by linarith
      rw [hLB3]
      have hstep : (k : ℝ) * (D * (Y / (L ^ B * L ^ 3))) ≤
          ((|K| + 1) * L) * (D * (Y / (L ^ B * L ^ 3))) :=
        mul_le_mul_of_nonneg_right hkL (by positivity)
      refine hstep.trans ?_
      have heq : ((|K| + 1) * L) * (D * (Y / (L ^ B * L ^ 3))) =
          ((|K| + 1) * D) * Y / (L ^ B * L ^ 2) := by
        field_simp
      rw [heq, div_le_iff₀ (by positivity)]
      calc (|K| + 1) * D * Y ≤ (0.000000005 * tailProduct * L ^ B) * Y :=
             mul_le_mul_of_nonneg_right hcL' hY0
           _ = 0.000000005 * L ^ B * (tailProduct * Y) := by ring
           _ ≤ 0.000000005 * L ^ B * (scale N Y n * L ^ 2) :=
             mul_le_mul_of_nonneg_left hmain (by positivity)
           _ = 0.000000005 * scale N Y n * (L ^ B * L ^ 2) := by ring
    linarith
  have hempty : (window N ε).filter (fun n =>
      0.00000001 * scale N Y n < ∑ j ∈ range k, t j n) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n hn
    exact not_lt.mpr (hsum_small n hn)
  have hunion := Feed578bBlocks19.sum_exceptional_card (window N ε) (range k) ee t
    (fun n => 0.00000001 * scale N Y n)
  rw [hempty, Finset.card_empty, Nat.cast_zero, add_zero] at hunion
  have hcardE : ∀ j ∈ range k,
      (((window N ε).filter (fun n => t j n < ee j n)).card : ℝ) ≤ |C| * A / L ^ (B + 3) := by
    intro j _
    obtain ⟨hM1, hM2⟩ := hM j N (by linarith)
    refine (hC N hN0 (M j N) (w j N) hM1 hM2 (hw j N) (hwp j N (by linarith))).trans ?_
    have hpos : 0 < L ^ (B + 3) := Real.rpow_pos_of_pos hL _
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hA) hpos.le
  have h4 := Finset.sum_le_card_nsmul (range k)
    (fun j => (((window N ε).filter (fun n => t j n < ee j n)).card : ℝ)) _ hcardE
  rw [card_range, nsmul_eq_mul] at h4
  refine hunion.trans (h4.trans ?_)
  rw [hLB3]
  have hx : 0 ≤ |C| * A / (L ^ B * L ^ 3) := by positivity
  calc (k : ℝ) * (|C| * A / (L ^ B * L ^ 3)) ≤ ((|K| + 1) * L) * (|C| * A / (L ^ B * L ^ 3)) :=
         mul_le_mul_of_nonneg_right hkL hx
       _ = (|K| + 1) * |C| * A / (L ^ B * L ^ 2) := by field_simp
       _ ≤ (|K| + 1) * |C| * A / L ^ B := by
         apply div_le_div_of_nonneg_left (by positivity) hLB
         exact le_mul_of_one_le_right hLB.le (one_le_pow₀ hL1)


#print axioms lemma19_uniform
#print axioms sum_exceptional_subset
#print axioms sum_exceptional_card
#print axioms ceil_blocks_le19
#print axioms lemma19_blocks_uniform_from_leaves
end
end LeanLab.Languasco2004.Feed578bBlocks19
