/-
P0069 Baker Harman Pintz 1997, pages 43 to 50, the bookkeeping behind every use of 5.2 in the
proof of Lemma 34. Burst burst-20261122, session S50, wave 3 on the leaves of
`upD52_lemma34_52`.

Two PROVED combination rules for the conclusion 5.2 of page 43 for the principal character,
written exactly in the form of `upD52_lemma34_52` in `Prep1122UpD52Split`.
1. `upD52_combine3`: if c = c1 - c2 - c3 on the interval J for all large x, then 5.2 for c1, c2,
   c3 gives 5.2 for c. This is the step "f_m satisfies 5.2, g_m satisfies 5.2" of page 49, the
   same argument as the end of `upD52_lemma34_52`, stated once for reuse.
2. `upD52_combine_blocks`: if c is a sum of at most log x pieces on J, each piece satisfying 5.2
   with one constant, then c satisfies 5.2. This is the dyadic step of page 49, "Let h_m be the
   contribution to g_m from n ~ N, p1 ~ P", and of the proof of Lemma 30, where the number of
   blocks is O(L) and is absorbed since A is arbitrary. Pointwise it is Cauchy's inequality
   |u_1 + ... + u_J|^2 <= J (|u_1|^2 + ... + |u_J|^2).
No new definition, no sorry. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52Split

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- Cauchy's inequality for J complex numbers: |u_1 + ... + u_J|^2 <= J sum |u_j|^2. PROVED. -/
theorem upD52_sq_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∑ j ∈ s, u j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖u j‖ ^ 2 := by
  calc ‖∑ j ∈ s, u j‖ ^ 2 ≤ (∑ j ∈ s, ‖u j‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ j ∈ s, ‖u j‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- One t range of 5.2 for a sum of J pieces: if b is the sum of d_0, ..., d_(J-1) on S, the
window integral of b is at most J times the sum of the window integrals of the pieces. PROVED. -/
theorem upD52_interval_blocks (S : Finset ℕ) (hS : ∀ m ∈ S, m ≠ 0) (χ : ℕ → ℂ)
    (b : ℕ → ℝ) (J : ℕ) (d : ℕ → ℕ → ℝ) (hb : ∀ m ∈ S, b m = ∑ j ∈ Finset.range J, d j m)
    (T a e : ℝ) (hae : a ≤ e) (h0 : ∀ t ∈ Set.uIcc a e, t ≠ 0) :
    (∫ t in a..e, ‖∑ m ∈ S, (b m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, (∫ t in a..e,
        ‖∑ m ∈ S, (d j m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          (T ^ 2 + t ^ 2)) := by
  have Id : ∀ j ∈ Finset.range J, IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ S, (d j m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) MeasureTheory.volume a e :=
    fun j _ => upD52_intble S hS χ (d j) T a e h0
  have Isum : IntervalIntegrable (fun t : ℝ => ∑ j ∈ Finset.range J,
      ‖∑ m ∈ S, (d j m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) MeasureTheory.volume a e := by
    have := IntervalIntegrable.sum (Finset.range J) Id
    convert this using 1
    funext t
    simp [Finset.sum_apply]
  rw [← intervalIntegral.integral_finsetSum Id, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hae (upD52_intble S hS χ b T a e h0)
    (Isum.const_mul _) (fun t _ => ?_)
  have hsum : (∑ m ∈ S, (b m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑ j ∈ Finset.range J, ∑ m ∈ S, (d j m : ℂ) * χ m /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hb m hm]
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hsum]
  have hd : 0 ≤ T ^ 2 + t ^ 2 := by positivity
  have hcs := upD52_sq_sum_le (Finset.range J) (fun j => ∑ m ∈ S, (d j m : ℂ) * χ m /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))
  rw [Finset.card_range] at hcs
  calc ‖∑ j ∈ Finset.range J, ∑ m ∈ S, (d j m : ℂ) * χ m /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)
      ≤ ((J : ℝ) * ∑ j ∈ Finset.range J, ‖∑ m ∈ S, (d j m : ℂ) * χ m /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T ^ 2 + t ^ 2) := by gcongr
    _ = (J : ℝ) * ∑ j ∈ Finset.range J, ‖∑ m ∈ S, (d j m : ℂ) * χ m /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2) := by
        rw [mul_div_assoc, Finset.sum_div]

/-- P0069 page 49: 5.2 of page 43 for the principal character passes from c1, c2, c3 to
c = c1 - c2 - c3, when that identity holds on J for all large x. The step "f_m and g_m satisfy
5.1 and 5.2" of the proof of Lemma 34, stated once. PROVED, by `upD52_interval` on each t range
and `upD52_reversed` when the t range is empty. -/
theorem upD52_combine3 {ε : ℝ} (c c1 c2 c3 : ℝ → ℕ → ℝ)
    (hsplit : ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ k ∈ rightInterval ε x,
      c x k = c1 x k - c2 x k - c3 x k)
    (h1 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c1 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c1 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A))
    (h2 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c2 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c2 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A))
    (h3 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c3 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c3 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨X0, hX0⟩ := hsplit
  obtain ⟨Cf, hCf⟩ := h1 A hA
  obtain ⟨C1, hC1⟩ := h2 A hA
  obtain ⟨C2, hC2⟩ := h3 A hA
  refine ⟨max (max (max X0 1) (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|)), ?_⟩
  intro x hx q hq1 hqQ
  have hCx : max (max X0 1) (max Cf (max C1 C2)) ≤ x := le_trans (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCx
  have hfx : Cf ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCx
  have h1x : C1 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hCx
  have h2x : C2 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hCx
  have hb := hX0 x hX0x
  have hS : ∀ m ∈ rightInterval ε x, m ≠ 0 := by
    intro m hm
    unfold rightInterval at hm
    rw [Finset.mem_Ioc] at hm
    omega
  set R := x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 with hRdef
  have hR : 0 ≤ R := by
    have : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    positivity
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hRL : 0 ≤ R * Real.log x ^ (-A) := mul_nonneg hR hL
  have hCbig : 3 * (|Cf| + |C1| + |C2|) ≤
      max (max (max X0 1) (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|)) := le_max_right _ _
  set Cbig := max (max (max X0 1) (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|))
    with hCbigdef
  have hfin : (3 * (|Cf| + |C1| + |C2|)) * (R * Real.log x ^ (-A)) ≤
      Cbig * (R * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hCbig hRL
  have habs : 0 ≤ 3 * (|Cf| + |C1| + |C2|) := by positivity
  set χ : ℕ → ℂ := fun m => (1 : DirichletCharacter ℂ q) (m : ZMod q) with hχ
  set T := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT
  set Y := x ^ (11 / 20 + ε) with hYdef
  set e := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hedef
  have he : 0 < e := Real.exp_pos _
  by_cases heY : e ≤ Y
  · have hneg : -Y ≤ -e := by linarith
    have h0n : ∀ t ∈ Set.uIcc (-Y) (-e), t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hneg] at ht
      have := ht.2
      intro h; rw [h] at this; linarith
    have h0p : ∀ t ∈ Set.uIcc e Y, t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le heY] at ht
      have := ht.1
      intro h; rw [h] at this; linarith
    have Jn := upD52_interval (rightInterval ε x) hS χ (c x) (c1 x) (c2 x) (c3 x) hb T
      (-Y) (-e) hneg h0n
    have Jp := upD52_interval (rightInterval ε x) hS χ (c x) (c1 x) (c2 x) (c3 x) hb T
      e Y heY h0p
    have Kf := hCf x hfx q hq1 hqQ
    have K1 := hC1 x h1x q hq1 hqQ
    have K2 := hC2 x h2x q hq1 hqQ
    have Kf' : Cf * R * Real.log x ^ (-A) ≤ |Cf| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    have K1' : C1 * R * Real.log x ^ (-A) ≤ |C1| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    have K2' : C2 * R * Real.log x ^ (-A) ≤ |C2| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    rw [mul_assoc]
    nlinarith
  · have hrev1 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) (-Y) (-e) (by linarith)
    have hrev2 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) e Y (by linarith)
    rw [mul_assoc]
    nlinarith

/-- P0069 page 49 and the proof of Lemma 30 on page 44: 5.2 of page 43 for the principal
character passes from dyadic pieces to their sum. If on J, for all large x, c is the sum of the
J(x) pieces d_0, ..., d_(J(x)-1) with J(x) at most log x, and the pieces satisfy 5.2 with one
constant, then c satisfies 5.2. The O(L) pieces cost a factor L^2, absorbed since A is
arbitrary. PROVED, by `upD52_interval_blocks`. -/
theorem upD52_combine_blocks {ε : ℝ} (c : ℝ → ℕ → ℝ) (d : ℝ → ℕ → ℕ → ℝ) (J : ℝ → ℕ)
    (hsplit : ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → (J x : ℝ) ≤ Real.log x ∧
      ∀ k ∈ rightInterval ε x, c x k = ∑ j ∈ Finset.range (J x), d x j k)
    (hd : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ j < J x, ∀ q : ℕ, 1 ≤ q →
      q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨X0, hX0⟩ := hsplit
  obtain ⟨C, hC⟩ := hd (A + 2) (by linarith)
  refine ⟨max (max X0 (max C 3)) |C|, ?_⟩
  intro x hx q hq1 hqQ
  have hX : max X0 (max C 3) ≤ x := le_trans (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_left _ _) hX
  have hCx : C ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hCabs : |C| ≤ max (max X0 (max C 3)) |C| := le_max_right _ _
  set Cbig := max (max X0 (max C 3)) |C| with hCbigdef
  obtain ⟨hJ, hb⟩ := hX0 x hX0x
  have hS : ∀ m ∈ rightInterval ε x, m ≠ 0 := by
    intro m hm
    unfold rightInterval at hm
    rw [Finset.mem_Ioc] at hm
    omega
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  set R := x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 with hRdef
  have hR : 0 ≤ R := by
    have : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
    positivity
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hLpos.le _
  have hLA2 : 0 ≤ Real.log x ^ (-(A + 2)) := Real.rpow_nonneg hLpos.le _
  have hpow : Real.log x ^ 2 * Real.log x ^ (-(A + 2)) = Real.log x ^ (-A) := by
    rw [show (Real.log x) ^ 2 = Real.log x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hLpos]
    congr 1; ring
  have hJ0 : (0 : ℝ) ≤ J x := Nat.cast_nonneg _
  have hJsq : (J x : ℝ) * J x ≤ Real.log x ^ 2 := by nlinarith
  have hfinal : (J x : ℝ) * J x * (C * R * Real.log x ^ (-(A + 2))) ≤
      Cbig * R * Real.log x ^ (-A) := by
    have h1 : C * R * Real.log x ^ (-(A + 2)) ≤ |C| * R * Real.log x ^ (-(A + 2)) := by
      have := mul_nonneg hR hLA2
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) this
    have h2 : 0 ≤ |C| * R * Real.log x ^ (-(A + 2)) := by positivity
    calc (J x : ℝ) * J x * (C * R * Real.log x ^ (-(A + 2)))
        ≤ (J x : ℝ) * J x * (|C| * R * Real.log x ^ (-(A + 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.log x ^ 2 * (|C| * R * Real.log x ^ (-(A + 2))) :=
          mul_le_mul_of_nonneg_right hJsq h2
      _ = |C| * R * (Real.log x ^ 2 * Real.log x ^ (-(A + 2))) := by ring
      _ = |C| * R * Real.log x ^ (-A) := by rw [hpow]
      _ ≤ Cbig * R * Real.log x ^ (-A) := by
          have := mul_nonneg hR hLA
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hCabs this
  have hCbig0 : 0 ≤ Cbig * R * Real.log x ^ (-A) := by
    have : 0 ≤ Cbig := le_trans (abs_nonneg _) hCabs
    positivity
  set χ : ℕ → ℂ := fun m => (1 : DirichletCharacter ℂ q) (m : ZMod q) with hχ
  set T := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT
  set Y := x ^ (11 / 20 + ε) with hYdef
  set e := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hedef
  have he : 0 < e := Real.exp_pos _
  by_cases heY : e ≤ Y
  · have hneg : -Y ≤ -e := by linarith
    have h0n : ∀ t ∈ Set.uIcc (-Y) (-e), t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hneg] at ht
      have := ht.2
      intro h; rw [h] at this; linarith
    have h0p : ∀ t ∈ Set.uIcc e Y, t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le heY] at ht
      have := ht.1
      intro h; rw [h] at this; linarith
    have Jn := upD52_interval_blocks (rightInterval ε x) hS χ (c x) (J x) (d x) hb T
      (-Y) (-e) hneg h0n
    have Jp := upD52_interval_blocks (rightInterval ε x) hS χ (c x) (J x) (d x) hb T
      e Y heY h0p
    have hblk : ∀ j ∈ Finset.range (J x),
        (∫ t in (-Y)..(-e), ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)) +
        (∫ t in e..Y, ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)) ≤
        C * R * Real.log x ^ (-(A + 2)) := fun j hj =>
      hC x hCx j (Finset.mem_range.mp hj) q hq1 hqQ
    have hsumb := Finset.sum_le_sum hblk
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumb
    calc _ ≤ (J x : ℝ) * ∑ j ∈ Finset.range (J x), (∫ t in (-Y)..(-e),
            ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)) +
          (J x : ℝ) * ∑ j ∈ Finset.range (J x), (∫ t in e..Y,
            ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)) := add_le_add Jn Jp
      _ = (J x : ℝ) * (∑ j ∈ Finset.range (J x), (∫ t in (-Y)..(-e),
            ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2)) +
          ∑ j ∈ Finset.range (J x), (∫ t in e..Y,
            ‖∑ m ∈ rightInterval ε x, (d x j m : ℂ) * χ m /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))) := by ring
      _ ≤ (J x : ℝ) * ((J x : ℝ) * (C * R * Real.log x ^ (-(A + 2)))) :=
          mul_le_mul_of_nonneg_left hsumb hJ0
      _ = (J x : ℝ) * J x * (C * R * Real.log x ^ (-(A + 2))) := by ring
      _ ≤ Cbig * R * Real.log x ^ (-A) := hfinal
  · have hrev1 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) (-Y) (-e) (by linarith)
    have hrev2 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) e Y (by linarith)
    linarith

end LeanLab.BHP1997.DecompC165d
