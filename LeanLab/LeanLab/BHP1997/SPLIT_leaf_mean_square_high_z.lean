/-
Split of `LeanLab.BHP1997.LowerShortC165.leaf_mean_square_high_z`, the mean square of display 1.9 on the longest windows,
into its principal character part and its non-principal part, as one NEW file.

P0069, Baker Harman Pintz 1997, page 52: display 5.18 is Lemma 29 applied to the short weight
for every character; for a non-principal character the main term vanishes, since the factor
delta is zero, and 5.18 is already the bound wanted. For the principal character the paper
needs 5.17, 5.19 to 5.23 to replace the contour main term W by the constant centre v0 over log Y.
The two leaves below are those two halves. The assembly also shows that for a modulus q above
a power of log x the principal character can be put into the exceptional family at no cost,
since the count of page 3 already allows one character there; so the principal leaf is only
asked for moduli up to that power of log x, the range of condition iii of Theorem 2.

The leaves are open; the glue and the assembly are complete and use no `sorry`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_lower_exceptional_mean_square

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-! ### Glue, fully proved -/

/-- Splitting a sum over the kept characters into the principal term and the rest. -/
theorem leaf_mean_square_high_z_glue_sum {q : ℕ} (E : Finset (DirichletCharacter ℂ q))
    (f : DirichletCharacter ℂ q → ℝ) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E, f χ ≤
      f 1 + ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E).filter
        (fun χ => χ ≠ 1), f χ := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E)
    (fun χ => χ = 1)]
  gcongr
  calc ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E).filter (fun χ => χ = 1), f χ
      ≤ ∑ χ ∈ ({1} : Finset (DirichletCharacter ℂ q)), f χ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro χ hχ
          simp only [Finset.mem_filter] at hχ
          simp [hχ.2]
        · intro χ _ _; exact hf χ
    _ = f 1 := by simp

/-- Dropping the principal character from the sum when it lies in the family. -/
theorem leaf_mean_square_high_z_glue_sum_mem {q : ℕ} (E : Finset (DirichletCharacter ℂ q))
    (f : DirichletCharacter ℂ q → ℝ) (h1 : (1 : DirichletCharacter ℂ q) ∈ E) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E, f χ =
      ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E).filter
        (fun χ => χ ≠ 1), f χ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun χ hχ => ?_)
  have : χ ≠ 1 := by
    intro h; subst h; simp [h1] at hχ
  simp [this]

/-- For a modulus at least `Real.log x ^ (4 * A)` one extra character costs nothing in the count
of page 3. -/
theorem leaf_mean_square_high_z_glue_one_le {A x : ℝ} {q : ℕ} (hx : 1 < x)
    (hq : Real.log x ^ (4 * A) < (q : ℝ)) :
    (1 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL4 : 0 ≤ Real.log x ^ (4 * A) := Real.rpow_nonneg hL.le _
  have h1 : (Real.log x ^ (4 * A)) ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hL4 hq.le (by norm_num)
  have h2 : (Real.log x ^ (4 * A)) ^ (1 / 2 : ℝ) = Real.log x ^ (2 * A) := by
    rw [← Real.rpow_mul hL.le]; ring_nf
  have h3 : Real.log x ^ (2 * A) * Real.log x ^ (-2 * A) = 1 := by
    rw [← Real.rpow_add hL]; simp
  have h4 : 0 ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hL.le _
  calc (1 : ℝ) = Real.log x ^ (2 * A) * Real.log x ^ (-2 * A) := h3.symm
    _ ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
        mul_le_mul_of_nonneg_right (h2 ▸ h1) h4

/-- Two bounds with constants `C1` and `C2` give one with any constant `C` at least
`C1 + C2`, for a nonnegative product of three factors. -/
theorem leaf_mean_square_high_z_glue_add {a b C1 C2 C r s t : ℝ} (ha : a ≤ C1 * r * s * t)
    (hb : b ≤ C2 * r * s * t) (hC : C1 + C2 ≤ C) (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    a + b ≤ C * r * s * t := by
  have hR : 0 ≤ r * s * t := mul_nonneg (mul_nonneg hr hs) ht
  have : (C1 + C2) * (r * s * t) ≤ C * (r * s * t) := mul_le_mul_of_nonneg_right hC hR
  nlinarith

/-! ### Leaves -/

/-- LEAF: the principal character part of display 1.9 on the longest windows, for moduli up to a power
of log x. P0069 page 52, displays 5.18, 5.22 and 5.23: Lemma 29 gives 5.18 with the contour main
term W, the prime number theorem form 5.17 with 5.19 and 5.20 gives 5.22, and 5.21 gives 5.23;
together they replace W by the constant centre v0 over log Y of condition iii, page 3 display 1.8.
Class: HARD -/
theorem leaf_mean_square_high_z_principal (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x → (q : ℝ) ≤ Real.log x ^ (4 * A) →
        ∀ z : ℝ, 2 * q * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
                  Thm2.delta (1 : DirichletCharacter ℂ q) * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the non-principal characters of display 1.9 on the longest windows, outside an exceptional
family with the count of page 3. P0069 page 52, display 5.18, Lemma 29 applied to the short
weight b0, for which conditions 5.1 and 5.2 were proved on pages 50 and 51; for a non-principal
character the factor delta is zero, so 5.18 is the bound itself.
Class: HARD -/
theorem leaf_mean_square_high_z_nonprincipal (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, 2 * q * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter
              (fun χ => χ ≠ 1),
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Assembly -/

theorem leaf_mean_square_high_z_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, 2 * q * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E1, hE1⟩ := leaf_mean_square_high_z_nonprincipal h4 h9 ω hω hz hε hε8
  have hP := leaf_mean_square_high_z_principal h4 h9 ω hω hz hε hε8
  refine ⟨fun A x q => if Real.log x ^ (4 * A) < (q : ℝ) then insert 1 (E1 A x q) else E1 A x q,
    fun A hA => ?_⟩
  obtain ⟨C1, hC1⟩ := hE1 A hA
  obtain ⟨C2, hC2⟩ := hP A hA
  set K : ℝ := |C1| + |C2| + 2 with hK
  refine ⟨K, fun x hx q hq hqQ => ?_⟩
  have hx1 : C1 ≤ x := by linarith [le_abs_self C1, abs_nonneg C2]
  have hx2 : C2 ≤ x := by linarith [le_abs_self C2, abs_nonneg C1]
  have hxg : 1 < x := by linarith [abs_nonneg C1, abs_nonneg C2]
  obtain ⟨hcard, hsum⟩ := hC1 x hx1 q hq hqQ
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hxg.le
  have hqh : (0:ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hl2 : (0:ℝ) ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hL0 _
  have hY : (0:ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hq2 : (0:ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := sq_nonneg _
  have hLA : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0 _
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  refine ⟨?_, fun z hzlo hzhi => ?_⟩
  · have hc1 : ((E1 A x q).card : ℝ) ≤ |C1| * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self C1) (mul_nonneg hqh hl2)
      calc ((E1 A x q).card : ℝ) ≤ C1 * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := hcard
        _ = C1 * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by ring
        _ ≤ _ := this
    have hKq : (|C1| + 1) * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) ≤
        K * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C2]) (mul_nonneg hqh hl2)
    dsimp only
    split_ifs with hbig
    · have hone := leaf_mean_square_high_z_glue_one_le (A := A) hxg hbig
      have hc : ((insert 1 (E1 A x q)).card : ℝ) ≤ ((E1 A x q).card : ℝ) + 1 := by
        exact_mod_cast Finset.card_insert_le _ _
      nlinarith
    · nlinarith
  · dsimp only
    have hint : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 := fun χ =>
      intervalIntegral.integral_nonneg hab (fun u _ => by positivity)
    have hs1 : ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E1 A x q).filter
              (fun χ => χ ≠ 1), ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
          |C1| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      refine (hsum z hzlo hzhi).trans ?_
      have := mul_le_mul_of_nonneg_right (le_abs_self C1) (mul_nonneg (mul_nonneg hq2 hY) hLA)
      linarith [this, show C1 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = C1 * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) by ring,
        show |C1| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = |C1| * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) by ring]
    have hKR : 0 ≤ K * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) -
        |C1| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      have : 0 ≤ (K - |C1|) * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        mul_nonneg (by linarith [abs_nonneg C2]) (mul_nonneg (mul_nonneg hq2 hY) hLA)
      linarith [this, show (K - |C1|) * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
        = K * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) -
        |C1| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) by ring]
    by_cases hbig : Real.log x ^ (4 * A) < (q : ℝ)
    · have hmem : (1 : DirichletCharacter ℂ q) ∈
          (if Real.log x ^ (4 * A) < (q : ℝ) then insert 1 (E1 A x q) else E1 A x q) := by
        rw [if_pos hbig]; exact Finset.mem_insert_self _ _
      rw [leaf_mean_square_high_z_glue_sum_mem _ _ hmem]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun χ _ _ => hint χ)) (by linarith)
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hχ ⊢
      rw [if_pos hbig] at hχ
      exact ⟨fun h => hχ.1 (Finset.mem_insert_of_mem h), hχ.2⟩
    · push_neg at hbig
      have hp := hC2 x hx2 q hq hqQ hbig z hzlo hzhi
      have hp' : ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
                  Thm2.delta (1 : DirichletCharacter ℂ q) * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
          |C2| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        refine hp.trans ?_
        have := mul_le_mul_of_nonneg_right (le_abs_self C2) (mul_nonneg (mul_nonneg hq2 hY) hLA)
        linarith [this, show C2 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
          = C2 * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) by ring,
          show |C2| * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
          = |C2| * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) by ring]
      have hE : (if Real.log x ^ (4 * A) < (q : ℝ) then insert 1 (E1 A x q) else E1 A x q) =
          E1 A x q := if_neg (not_lt.mpr hbig)
      rw [hE]
      refine ((leaf_mean_square_high_z_glue_sum (E1 A x q) _ hint)).trans ?_
      exact leaf_mean_square_high_z_glue_add hp' hs1 (by linarith) hq2 hY hLA

end LeanLab.BHP1997.LowerShortC165
