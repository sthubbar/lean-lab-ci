/-
Split unit for `leaf_nonmaximal_exceptional_summand_decay` of
LeanLab/Linnik/Decomp498a.lean. This file adds new declarations only: no existing
statement is edited, and the parent keeps its sorry.

Source: Gallagher 1975 Invent. Math. 29 p.131 display 14 and the paragraph after it,
"it follows by the method of [10, Section 7]", where [10] is Gallagher 1970 Invent. Math. 11
329-339, and there p.336 to 337 display 27, the Deuring-Heilbronn widening of the zero free
region 26 in the presence of an exceptional zero.

Route. In the nonmaximal case the character has two real zeros gamma < gamma' in the lab's
fixed strip of width exceptionalStrip. Display 27 of Gallagher 1970 forces every zero of
that character other than a zero in the strip to lie left of 1 - delta / log T, for a fixed
delta depending on the strip width. Then
1. the corrected coefficient splits as the uncorrected coefficient plus the exceptional main
   coefficient of gamma, because gamma is a zero;
2. the uncorrected single summand is bounded as in the nonexceptional case of display 14;
3. the exceptional main coefficient of gamma, with gamma left of 1 - delta / log T, has a
   window norm with the same exponential saving;
4. Minkowski's inequality on the window norm adds the two bounds.
Steps 1 and 4 and the case analysis are proved here; the three LEAF theorems carry the rest.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp498a

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- LEAF: Deuring-Heilbronn repulsion, Gallagher 1970 Invent. Math. 11 p.336 to 337 display 27.
Class: HARD.
Display 27 widens the zero free region 26 and is cited by Gallagher 1975 p.131 after display 14 as
"the method of [10, Section 7]" and "an even stronger bound". If a primitive L function of
conductor at most T has a zero in the rectangle of width exceptionalStrip over log T and
height T, then every other zero in that height range lies left of 1 - delta over log T, for
a fixed positive delta depending only on the strip width. In the source: a zero right of
1 - delta / log T with delta small is the exceptional zero 1 - delta of display 26, and
display 27 then pushes every other zero left of 1 - c2 log of e c1 over delta log T, which is
left of the strip once delta is small. -/
theorem leaf_deuring_heilbronn_other_zero :
    ∃ δ T₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)), χ.IsPrimitive → (q : ℝ) + 1 ≤ T →
        ∀ ρ₁ ρ₂ : ℂ, χ.LFunction ρ₁ = 0 → χ.LFunction ρ₂ = 0 → ρ₁ ≠ ρ₂ →
          |ρ₁.im| ≤ T → |ρ₂.im| ≤ T → 1 - exceptionalStrip / Real.log T ≤ ρ₂.re →
          ρ₁.re < 1 - δ / Real.log T := by
  sorry

/-- LEAF: single summand of the nonexceptional case, Gallagher 1975 p.131 display 14.
Class: MEDIUM.
Gallagher 1975 Invent. Math. 29 p.131 display 14. For a primitive character of conductor at most P = N^θ carrying a real zero in the fixed
strip at height T = P^5, and with no zero right of 1 - delta / log T up to height T, the
uncorrected single summand of display 14 is at most C exp of minus c over theta times
sqrt N over log N. Intended proof: by `Decomp1532b.page_subsingleton` at the strip width,
no other primitive character of conductor at most T has a zero in the strip, so the gap
hypothesis of `ExplicitFormula.mean_decay_nonexceptional` holds at width min delta
exceptionalStrip for every conductor at most P; take the single summand of that proved sum. -/
theorem leaf_single_summand_nonexceptional (δ : ℝ) (hδ : 0 < δ) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ →
          (∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 →
            ρ.re < 1 - δ / Real.log (((N : ℝ) ^ θ) ^ 5)) →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ 0 0) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  have hb0 : 0 < min δ exceptionalStrip := lt_min hδ exceptionalStrip_pos
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hnon⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_nonexceptional (min δ exceptionalStrip) hb0
  refine ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hnon θ hθ hθle
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₁ N₂, fun N hN q χ γ hp hq hz hlo hgapχ => ?_⟩
  set P := (N : ℝ) ^ θ with hPdef
  have hP2 : 2 ≤ P := hN₂ N ((le_max_right _ _).trans hN)
  have hPT : P ≤ P ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
  have hT2 : 2 ≤ P ^ 5 := hP2.trans hPT
  have hlogT : 0 < Real.log (P ^ 5) := Real.log_pos (by linarith)
  have hx : (⟨q, χ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
      excSet exceptionalStrip (P ^ 5) := by
    refine ⟨hq.trans hPT, hp, (γ : ℂ), hz, ?_, ?_⟩
    · simpa only [Complex.ofReal_re] using hlo
    · simp only [Complex.ofReal_im, abs_zero]; positivity
  have hδb : 1 - δ / Real.log (P ^ 5) ≤ 1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
    have := div_le_div_of_nonneg_right (min_le_left δ exceptionalStrip) hlogT.le
    linarith
  have hesb : 1 - exceptionalStrip / Real.log (P ^ 5) ≤
      1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
    have := div_le_div_of_nonneg_right (min_le_right δ exceptionalStrip) hlogT.le
    linarith
  have hsub := Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton
  have hbs : exceptionalStrip ≤ Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hgap : ∀ k < ⌊P⌋₊, ∀ ψ : DirichletCharacter ℂ (k + 1), ψ.IsPrimitive →
      ∀ ρ : ℂ, ψ.LFunction ρ = 0 → |ρ.im| ≤ P ^ 5 →
        ρ.re < 1 - min δ exceptionalStrip / Real.log (P ^ 5) := by
    intro k hk ψ hψ ρ hρ him
    by_cases hkx : (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q, χ⟩
    · obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hkx
      obtain rfl := eq_of_heq hh
      exact (hgapχ ρ hρ him).trans_le hδb
    · by_contra hge
      push_neg at hge
      have hkP : ((k + 1 : ℕ) : ℝ) ≤ P :=
        (Nat.le_floor_iff (by linarith)).mp (Nat.succ_le_of_lt hk)
      have hmem : (⟨k, ψ⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) ∈
          excSet exceptionalStrip (P ^ 5) := by
        refine ⟨?_, hψ, ρ, hρ, hesb.trans hge, him⟩
        push_cast at hkP
        show (k : ℝ) + 1 ≤ P ^ 5
        linarith
      exact hkx (hsub.2 (P ^ 5) hT2 (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hmem)
        (LeanLab.Linnik.Decomp1532b.excSet_mono hbs hT2 hx))
  have htotal := hN₁ N ((le_max_left _ _).trans hN) hgap
  have hqK : q < ⌊P⌋₊ := by
    have : q + 1 ≤ ⌊P⌋₊ :=
      (Nat.le_floor_iff (show (0 : ℝ) ≤ P by positivity)).mpr (by exact_mod_cast hq)
    omega
  change (∑ k ∈ range ⌊P⌋₊,
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
        Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1)
              (gallagherLength N θ) m‖ ^ 2)) ≤ _ at htotal
  apply le_trans ?_ htotal
  calc
    _ ≤ ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun ψ => ψ.IsPrimitive), Real.pi / (2 * gallagherLength N θ) *
          Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
            ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1)
              (gallagherLength N θ) m‖ ^ 2) :=
      single_le_sum (fun ψ _ => by positivity) (mem_filter.mpr ⟨mem_univ χ, hp⟩)
    _ ≤ _ := by
      apply single_le_sum (f := fun k : ℕ =>
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun ψ => ψ.IsPrimitive),
          Real.pi / (2 * gallagherLength N θ) *
            Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
              ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient ψ 0 0) (N + 1)
                (gallagherLength N θ) m‖ ^ 2))
        (fun k _ => sum_nonneg fun ψ _ => by positivity) (mem_range.mpr hqK)

/-- Gallagher window norm against the plain l2 norm: each window holds at most L terms and
each index lies in at most L windows. -/
lemma nmx_win_sq_sum_le (a : ℕ → ℂ) (M L : ℕ) :
    ∑ m ∈ range (M + L), ‖LeanLab.PNTPort.Gallagher.win a M L m‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ∑ n ∈ range M, ‖a n‖ ^ 2 := by
  classical
  have h1 : ∀ m, ‖LeanLab.PNTPort.Gallagher.win a M L m‖ ^ 2 ≤
      (L : ℝ) * ∑ n ∈ (range M).filter (fun n => n ≤ m ∧ m < n + L), ‖a n‖ ^ 2 := by
    intro m
    unfold LeanLab.PNTPort.Gallagher.win
    set s := (range M).filter (fun n => n ≤ m ∧ m < n + L)
    have hcard : (s.card : ℝ) ≤ L := by
      have hsub : s ⊆ Ico (m + 1 - L) (m + 1) := by
        intro n hn
        simp only [s, mem_filter, mem_range] at hn
        simp only [mem_Ico]
        omega
      have := card_le_card hsub
      rw [Nat.card_Ico] at this
      exact_mod_cast this.trans (by omega)
    calc ‖∑ n ∈ s, a n‖ ^ 2 ≤ (∑ n ∈ s, ‖a n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (L : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sum_nonneg fun n _ => sq_nonneg _)
  have h2 : ∀ n ∈ range M,
      ∑ m ∈ range (M + L), (if n ≤ m ∧ m < n + L then ‖a n‖ ^ 2 else 0) ≤
        (L : ℝ) * ‖a n‖ ^ 2 := by
    intro n _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hsub : (range (M + L)).filter (fun m => n ≤ m ∧ m < n + L) ⊆ Ico n (n + L) := by
      intro m hm
      simp only [mem_filter, mem_range] at hm
      simp only [mem_Ico]
      omega
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast this.trans (by omega)
  calc ∑ m ∈ range (M + L), ‖LeanLab.PNTPort.Gallagher.win a M L m‖ ^ 2
      ≤ ∑ m ∈ range (M + L), (L : ℝ) *
          ∑ n ∈ (range M).filter (fun n => n ≤ m ∧ m < n + L), ‖a n‖ ^ 2 :=
        sum_le_sum fun m _ => h1 m
    _ = (L : ℝ) * ∑ n ∈ range M,
          ∑ m ∈ range (M + L), (if n ≤ m ∧ m < n + L then ‖a n‖ ^ 2 else 0) := by
        rw [← mul_sum]
        congr 1
        simp_rw [sum_filter]
        exact sum_comm
    _ ≤ (L : ℝ) * ∑ n ∈ range M, (L : ℝ) * ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum h2) (Nat.cast_nonneg _)
    _ = (L : ℝ) ^ 2 * ∑ n ∈ range M, ‖a n‖ ^ 2 := by rw [← mul_sum]; ring

/-- LEAF: window bound for the main polynomial T tilde, Gallagher 1975 p.131 after display 14.
Class: MEDIUM.
Gallagher 1975 Invent. Math. 29 p.131, the bound on T tilde of a real zero with the saving of
display 14. If gamma lies left of 1 - delta / log T with
T = P^5 and P = N^θ, the Gallagher window norm of the coefficients m^(gamma - 1) / log m,
1 < m, is at most C exp of minus c over theta times sqrt N over log N. Elementary: windows
inside m at least sqrt N have terms at most exp of minus delta over 10 theta, and the
windows meeting m below sqrt N number at most sqrt N + L and cost N^(-θ/2) log N relatively. -/
theorem leaf_exceptional_main_window (δ : ℝ) (hδ : 0 < δ) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ γ : ℝ, γ < 1 - δ / Real.log (((N : ℝ) ^ θ) ^ 5) →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win
                  (fun m : ℕ => if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0)
                  (N + 1) (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  refine ⟨δ / 10, 2 * Real.pi, 1 / 2, by positivity, by positivity, by norm_num, le_refl _,
    fun θ hθ _ => ?_⟩
  set e := Real.exp (-(δ / 10) / θ) with he
  have he0 : 0 < e := Real.exp_pos _
  set κ := e ^ 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε := Real.sqrt κ * Real.log 2 with hε
  have hε0 : 0 < ε := mul_pos (Real.sqrt_pos.mpr hκ0) hl2
  have hev1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound hε0
  have hev2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (hev1.and hev2))
  refine ⟨N₀, fun N hN γ hγ => ?_⟩
  obtain ⟨hlo, hN2⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogT : Real.log (((N : ℝ) ^ θ) ^ 5) = 5 * (θ * Real.log N) := by
    rw [Real.log_pow, Real.log_rpow hN0]; push_cast; ring
  have hlogT0 : 0 < Real.log (((N : ℝ) ^ θ) ^ 5) := by rw [hlogT]; positivity
  have hγ1 : γ < 1 := by
    have : 0 < δ / Real.log (((N : ℝ) ^ θ) ^ 5) := div_pos hδ hlogT0
    linarith
  set E : ℕ → ℂ := fun m : ℕ =>
    if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0 with hEdef
  -- termwise bound
  have hterm : ∀ n ∈ range (N + 1), ‖E n‖ ^ 2 ≤
      (if n * n ≤ N then 1 / Real.log 2 ^ 2 else 0) + 4 * κ / Real.log N ^ 2 := by
    intro n _
    have hB0 : 0 ≤ 4 * κ / Real.log N ^ 2 := by positivity
    by_cases h1 : 1 < n
    · simp only [hEdef, h1, if_true]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h1
      have hn0 : (0 : ℝ) < n := by linarith
      have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
      have hx1 : (n : ℝ) ^ (γ - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have hx0 : 0 ≤ (n : ℝ) ^ (γ - 1) := Real.rpow_nonneg hn0.le _
      split_ifs with hsq
      · have hq : (n : ℝ) ^ (γ - 1) / Real.log n ≤ 1 / Real.log 2 :=
          div_le_div₀ zero_le_one hx1 hl2 hlogn
        have hq0 : 0 ≤ (n : ℝ) ^ (γ - 1) / Real.log n := div_nonneg hx0 (by linarith)
        have := pow_le_pow_left₀ hq0 hq 2
        simp only [div_pow, one_pow] at this
        rw [div_pow]
        linarith
      · push_neg at hsq
        have hNn : (N : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast hsq.le
        have hlNn : Real.log N ≤ 2 * Real.log n := by
          have := Real.log_le_log hN0 hNn
          rw [Real.log_mul hn0.ne' hn0.ne'] at this
          linarith
        have hexpo : Real.log n * (γ - 1) ≤ -(δ / 10) / θ := by
          have hd : γ - 1 ≤ -(δ / Real.log (((N : ℝ) ^ θ) ^ 5)) := by linarith
          rw [hlogT] at hd
          have hln0 : 0 ≤ Real.log n := by linarith
          have h3 : Real.log n * (γ - 1) ≤ Real.log n * (-(δ / (5 * (θ * Real.log N)))) :=
            mul_le_mul_of_nonneg_left hd hln0
          have h4 : Real.log n * (δ / (5 * (θ * Real.log N))) ≥
              (Real.log N / 2) * (δ / (5 * (θ * Real.log N))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have h5 : (Real.log N / 2) * (δ / (5 * (θ * Real.log N))) = (δ / 10) / θ := by
            field_simp; ring
          rw [mul_neg] at h3
          rw [neg_div]
          linarith
        have hxe : (n : ℝ) ^ (γ - 1) ≤ e := by
          rw [Real.rpow_def_of_pos hn0, he]
          exact Real.exp_le_exp.mpr hexpo
        have hlogn2 : Real.log N / 2 ≤ Real.log n := by linarith
        have hq : (n : ℝ) ^ (γ - 1) / Real.log n ≤ e / (Real.log N / 2) :=
          div_le_div₀ he0.le hxe (by positivity) hlogn2
        have hq0 : 0 ≤ (n : ℝ) ^ (γ - 1) / Real.log n := div_nonneg hx0 (by linarith)
        have := pow_le_pow_left₀ hq0 hq 2
        have h6 : (e / (Real.log N / 2)) ^ 2 = 4 * κ / Real.log N ^ 2 := by
          rw [hκ]; field_simp; ring
        rw [h6] at this
        linarith
    · simp only [hEdef, h1, if_false, norm_zero]
      have hz : (0 : ℝ) ≤ 1 / Real.log 2 ^ 2 := by positivity
      have hz' : (0 : ℝ) ≤ (Real.log 2 ^ 2)⁻¹ := by positivity
      split_ifs <;> norm_num <;> linarith
  -- the count of small indices
  have hsmall : ∑ n ∈ range (N + 1), (if n * n ≤ N then 1 / Real.log 2 ^ 2 else 0) ≤
      ((Nat.sqrt N : ℝ) + 1) * (1 / Real.log 2 ^ 2) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hsub : (range (N + 1)).filter (fun n => n * n ≤ N) ⊆ range (Nat.sqrt N + 1) := by
      intro n hn
      simp only [mem_filter, mem_range] at hn ⊢
      have := Nat.le_sqrt.mpr hn.2
      omega
    have := card_le_card hsub
    rw [card_range] at this
    exact_mod_cast this
  set S := ∑ n ∈ range (N + 1), ‖E n‖ ^ 2 with hS
  have hS1 : S ≤ ((Nat.sqrt N : ℝ) + 1) * (1 / Real.log 2 ^ 2) +
      ((N : ℝ) + 1) * (4 * κ / Real.log N ^ 2) := by
    have := sum_le_sum hterm
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at this
    push_cast at this
    linarith
  -- the small indices are negligible for large N
  have hsq1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hns : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hlo' : Real.log N ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := hlo
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogN,
      abs_of_nonneg (Real.rpow_nonneg hN0.le _)] at h
    exact h
  have hq4 : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlog2 : Real.log N ^ 2 ≤ ε ^ 2 * Real.sqrt N := by
    have := pow_le_pow_left₀ hlogN.le hlo' 2
    rw [mul_pow, hq4] at this
    exact this
  have hε2 : ε ^ 2 = κ * Real.log 2 ^ 2 := by
    rw [hε, mul_pow, Real.sq_sqrt hκ0.le]
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hA : ((Nat.sqrt N : ℝ) + 1) * (1 / Real.log 2 ^ 2) ≤ 8 * κ * N / Real.log N ^ 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((Nat.sqrt N : ℝ) + 1) ≤ 2 * Real.sqrt N := by linarith
    calc ((Nat.sqrt N : ℝ) + 1) * Real.log N ^ 2
        ≤ (2 * Real.sqrt N) * (ε ^ 2 * Real.sqrt N) :=
          mul_le_mul h1 hlog2 (by positivity) (by positivity)
      _ = 2 * κ * N * Real.log 2 ^ 2 := by rw [hε2]; nlinarith [hsN]
      _ ≤ 8 * κ * N * Real.log 2 ^ 2 := by
          have : 0 ≤ κ * N * Real.log 2 ^ 2 := by positivity
          nlinarith
  have hB : ((N : ℝ) + 1) * (4 * κ / Real.log N ^ 2) ≤ 8 * κ * N / Real.log N ^ 2 := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hS2 : S ≤ (4 * e * (Real.sqrt N / Real.log N)) ^ 2 := by
    have : (4 * e * (Real.sqrt N / Real.log N)) ^ 2 = 16 * κ * N / Real.log N ^ 2 := by
      rw [hκ, show (4 * e * (Real.sqrt N / Real.log N)) ^ 2 =
        16 * e ^ 2 * (Real.sqrt N ^ 2) / Real.log N ^ 2 by ring, Real.sq_sqrt hN0.le]
    rw [this]
    have h16 : 8 * κ * N / Real.log N ^ 2 + 8 * κ * N / Real.log N ^ 2 =
        16 * κ * N / Real.log N ^ 2 := by ring
    linarith
  have hsqS : Real.sqrt S ≤ 4 * e * (Real.sqrt N / Real.log N) := by
    calc Real.sqrt S ≤ Real.sqrt ((4 * e * (Real.sqrt N / Real.log N)) ^ 2) :=
          Real.sqrt_le_sqrt hS2
      _ = _ := Real.sqrt_sq (by positivity)
  -- window step
  set L := gallagherLength N θ with hL
  have hwin := nmx_win_sq_sum_le E (N + 1) L
  have hS0 : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hroot : Real.sqrt (∑ m ∈ range (N + 1 + L),
      ‖LeanLab.PNTPort.Gallagher.win E (N + 1) L m‖ ^ 2) ≤ (L : ℝ) * Real.sqrt S := by
    calc _ ≤ Real.sqrt ((L : ℝ) ^ 2 * S) := Real.sqrt_le_sqrt hwin
      _ = (L : ℝ) * Real.sqrt S := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  have hLL : Real.pi / (2 * (L : ℝ)) * L ≤ Real.pi / 2 := by
    have h : Real.pi / (2 * (L : ℝ)) * L = Real.pi / 2 * ((L : ℝ) / L) := by ring
    rw [h]
    exact mul_le_of_le_one_right (by positivity) (div_self_le_one _)
  have hpi : 0 ≤ Real.pi / (2 * (L : ℝ)) := by positivity
  calc Real.pi / (2 * (L : ℝ)) * Real.sqrt (∑ m ∈ range (N + 1 + L),
        ‖LeanLab.PNTPort.Gallagher.win E (N + 1) L m‖ ^ 2)
      ≤ Real.pi / (2 * (L : ℝ)) * ((L : ℝ) * Real.sqrt S) :=
        mul_le_mul_of_nonneg_left hroot hpi
    _ = (Real.pi / (2 * (L : ℝ)) * L) * Real.sqrt S := by ring
    _ ≤ Real.pi / 2 * (4 * e * (Real.sqrt N / Real.log N)) :=
        mul_le_mul hLL hsqS (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * Real.pi * e * (Real.sqrt N / Real.log N) := by ring

/-! ### Proved helpers -/

/-- Minkowski's inequality for a finite sum of squared complex norms. -/
lemma nmx_sqrt_sum_norm_add_sq_le (s : Finset ℕ) (a b : ℕ → ℂ) :
    Real.sqrt (∑ m ∈ s, ‖a m + b m‖ ^ 2) ≤
      Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2) := by
  have hA : 0 ≤ ∑ m ∈ s, ‖a m‖ ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hB : 0 ≤ ∑ m ∈ s, ‖b m‖ ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hcs : (∑ m ∈ s, ‖a m‖ * ‖b m‖) ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * ∑ m ∈ s, ‖b m‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq s _ _
  have hcs' : ∑ m ∈ s, ‖a m‖ * ‖b m‖ ≤
      Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) * Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2) := by
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  have hpt : ∑ m ∈ s, ‖a m + b m‖ ^ 2 ≤
      ∑ m ∈ s, ‖a m‖ ^ 2 + 2 * ∑ m ∈ s, ‖a m‖ * ‖b m‖ + ∑ m ∈ s, ‖b m‖ ^ 2 := by
    calc ∑ m ∈ s, ‖a m + b m‖ ^ 2
        ≤ ∑ m ∈ s, (‖a m‖ ^ 2 + 2 * (‖a m‖ * ‖b m‖) + ‖b m‖ ^ 2) := by
          apply sum_le_sum
          intro m _
          have h := norm_add_le (a m) (b m)
          have h0 := norm_nonneg (a m + b m)
          nlinarith [norm_nonneg (a m), norm_nonneg (b m)]
      _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have hsq : ∑ m ∈ s, ‖a m‖ ^ 2 + 2 * ∑ m ∈ s, ‖a m‖ * ‖b m‖ + ∑ m ∈ s, ‖b m‖ ^ 2 ≤
      (Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2)) ^ 2 := by
    have e1 := Real.sq_sqrt hA
    have e2 := Real.sq_sqrt hB
    nlinarith
  calc Real.sqrt (∑ m ∈ s, ‖a m + b m‖ ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ m ∈ s, ‖a m‖ ^ 2) + Real.sqrt (∑ m ∈ s, ‖b m‖ ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt (hpt.trans hsq)
    _ = _ := Real.sqrt_sq (by positivity)

/-- The Gallagher window is additive in the coefficient sequence. -/
lemma nmx_win_add (f g : ℕ → ℂ) (N L m : ℕ) :
    LeanLab.PNTPort.Gallagher.win (fun n => f n + g n) N L m =
      LeanLab.PNTPort.Gallagher.win f N L m + LeanLab.PNTPort.Gallagher.win g N L m := by
  unfold LeanLab.PNTPort.Gallagher.win
  rw [sum_add_distrib]

/-- Gallagher 1975 p.131: at a zero gamma, the corrected coefficient at conductor q + 1 is
the uncorrected coefficient plus the exceptional main coefficient of gamma. -/
lemma nmx_correctedCoefficient_split {q : ℕ} (χ : DirichletCharacter ℂ (q + 1))
    (γ : ℝ) (hz : χ.LFunction (γ : ℂ) = 0) :
    correctedCoefficient χ (q + 1) γ = fun m => correctedCoefficient χ 0 0 m +
      (if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0) := by
  funext m
  unfold correctedCoefficient
  have h0 : ¬ (q + 1 = 0 ∧ χ.LFunction ((0 : ℝ) : ℂ) = 0) := fun h => Nat.succ_ne_zero q h.1
  rw [_root_.if_pos (show q + 1 = q + 1 ∧ χ.LFunction (γ : ℂ) = 0 from ⟨rfl, hz⟩),
    _root_.if_neg h0, add_zero]

/-- Adding two exponentially decaying bounds at a common rate. -/
lemma nmx_add_two_exponential_bounds {E₁ E₂ c c₁ c₂ C₁ C₂ θ s : ℝ} (hθ : 0 < θ)
    (hs : 0 ≤ s) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂)
    (h₁ : E₁ ≤ C₁ * Real.exp (-c₁ / θ) * s)
    (h₂ : E₂ ≤ C₂ * Real.exp (-c₂ / θ) * s) :
    E₁ + E₂ ≤ (C₁ + C₂) * Real.exp (-c / θ) * s := by
  have hexp₁ : Real.exp (-c₁ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hexp₂ : Real.exp (-c₂ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have h₁' : E₁ ≤ C₁ * Real.exp (-c / θ) * s :=
    h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₁ hC₁) hs)
  have h₂' : E₂ ≤ C₂ * Real.exp (-c / θ) * s :=
    h₂.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₂ hC₂) hs)
  have hsplit : C₁ * Real.exp (-c / θ) * s + C₂ * Real.exp (-c / θ) * s
      = (C₁ + C₂) * Real.exp (-c / θ) * s := by ring
  linarith

/-! ### Assembly -/

/-- The parent statement `leaf_nonmaximal_exceptional_summand_decay` of
LeanLab/Linnik/Decomp498a.lean, same statement text, proved from the three leaves above.
The parent theorem is neither used nor restated as a hypothesis. -/
theorem leaf_nonmaximal_exceptional_summand_decay_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (γ : ℝ),
          χ.IsPrimitive → (q : ℝ) + 1 ≤ (N : ℝ) ^ θ → χ.LFunction (γ : ℂ) = 0 →
          1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          (∃ γ' : ℝ, χ.LFunction (γ' : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ' ∧ γ' < 1 ∧ γ < γ') →
          Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (q + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  obtain ⟨δ, T₀, hδ, hDH⟩ := leaf_deuring_heilbronn_other_zero
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hB⟩ := leaf_single_summand_nonexceptional δ hδ
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hE⟩ := leaf_exceptional_main_window δ hδ
  refine ⟨min c₁ c₂, C₁ + C₂, min θ₁ θ₂, lt_min hc₁ hc₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁2, fun θ hθ hθle => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hB θ hθ (hθle.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hE θ hθ (hθle.trans (min_le_right _ _))
  have hev : ∀ᶠ N : ℕ in atTop, max T₀ 2 ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN q χ γ hp hq hz hlo hlt hmore => ?_⟩
  have hN1' : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2' : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3' : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  set P := (N : ℝ) ^ θ with hPdef
  have hPm : max T₀ 2 ≤ P := hN₃ N hN3'
  have hP1 : 1 ≤ P := by linarith [le_max_right T₀ 2]
  have hPT : P ≤ P ^ 5 := le_self_pow₀ hP1 (by norm_num)
  have hT₀ : T₀ ≤ P ^ 5 := (le_max_left T₀ 2).trans (hPm.trans hPT)
  have hqT : (q : ℝ) + 1 ≤ P ^ 5 := hq.trans hPT
  obtain ⟨γ', hz', hlo', hlt', hγγ'⟩ := hmore
  have hne : ((γ' : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
    intro h
    have := Complex.ofReal_inj.mp h
    linarith
  have hγ'gap : γ' < 1 - δ / Real.log (P ^ 5) := by
    have h := hDH (P ^ 5) hT₀ q χ hp hqT (γ' : ℂ) (γ : ℂ) hz' hz hne
      (by simp only [Complex.ofReal_im, abs_zero]; positivity)
      (by simp only [Complex.ofReal_im, abs_zero]; positivity)
      (by simpa only [Complex.ofReal_re] using hlo)
    simpa only [Complex.ofReal_re] using h
  have hγgap : γ < 1 - δ / Real.log (P ^ 5) := hγγ'.trans hγ'gap
  have hgap : ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ P ^ 5 →
      ρ.re < 1 - δ / Real.log (P ^ 5) := by
    intro ρ hρ him
    by_cases hργ : ρ = (γ : ℂ)
    · subst hργ
      simpa only [Complex.ofReal_re] using hγgap
    · exact hDH (P ^ 5) hT₀ q χ hp hqT ρ (γ : ℂ) hρ hz hργ him
        (by simp only [Complex.ofReal_im, abs_zero]; positivity)
        (by simpa only [Complex.ofReal_re] using hlo)
  have hb₁ := hN₁ N hN1' q χ γ hp hq hz hlo hgap
  have hb₂ := hN₂ N hN2' γ hγgap
  rw [nmx_correctedCoefficient_split χ γ hz]
  simp_rw [nmx_win_add]
  have hpi : 0 ≤ Real.pi / (2 * (gallagherLength N θ : ℝ)) := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  refine (mul_le_mul_of_nonneg_left (nmx_sqrt_sum_norm_add_sq_le _ _ _) hpi).trans ?_
  rw [mul_add]
  exact nmx_add_two_exponential_bounds hθ hs hC₁.le hC₂.le (min_le_left _ _)
    (min_le_right _ _) hb₁ hb₂

end LeanLab.Linnik.Decomp486c

#print axioms LeanLab.Linnik.Decomp486c.leaf_nonmaximal_exceptional_summand_decay_split
