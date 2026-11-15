/-
DEAD SPLIT. Unit U-1622, 2026-11-06. Do not work on any leaf in this file.
Reason: the conclusion of local_prime_mass357 is false. At q equal to 2 and a equal to 1 the
arc about 1/2 carries mass above N over log cubed N, far above the allowed bound.
Audit1622.not_leafLocalMass states this, build pending at the return of U-1622. Equation 9.1 of P0093 is used
only for q above Q equal to N to one tenth, and this leaf dropped that condition.
Live route: doubled_system_mass376 in Decomp376c, and its re-cut in SPLIT1622_exceptional.
Statements below are unchanged. This file is not on the route of linnik1951_decomposed412.
-/
/-
Split of the exceptional prime mass estimate used by the binary Goldbach circle
method. The sealed target exceptional_prime_mass357 stays untouched in
Decomp357c; this file states the smaller steps it is assembled from and proves
the target from them under the same hypotheses.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357c
import LeanLab.Linnik1951.Measure435

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology BigOperators

/-! ## Step 1: Dirichlet at level `tau`, with the denominator at least two

Inside the exceptional set the point is outside the major arcs, so the Dirichlet
approximant cannot have denominator one (that would put it in a major arc), and a
reduced denominator divides no numerator. -/
private theorem rat_arc_cover357 (N : ℕ) (hN : 1 ≤ N) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hmaj : α ∉ majorArcs280 N) :
    ∃ q : ℕ, ∃ a : ℤ, 2 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      ¬ ((q : ℤ) ∣ a) ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hN1 (by norm_num)
  set n : ℕ := ⌊τ⌋₊ with hndef
  have hnpos : 0 < n := Nat.floor_pos.mpr hτ1
  have hnτ : τ ≤ (n : ℝ) + 1 := Nat.lt_floor_add_one τ |>.le
  have hτn : (n : ℝ) ≤ τ := Nat.floor_le hτpos.le
  obtain ⟨r, hbd, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hnpos
  have hdenpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hrr : (r.num : ℝ) / (r.den : ℝ) = (r : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.num_div_den r)
    simpa using h
  -- the Dirichlet error at the floor level is at most the leaf's radius
  have hclose : |α - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / ((r.den : ℝ) * τ) := by
    rw [← hrr] at hbd
    refine hbd.trans ?_
    apply one_div_le_one_div_of_le (mul_pos hdenpos hτpos)
    calc (r.den : ℝ) * τ ≤ (r.den : ℝ) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hnτ hdenpos.le
      _ = ((n : ℝ) + 1) * (r.den : ℝ) := by ring
  have hdenle : (r.den : ℝ) ≤ τ := by
    have h1 : (r.den : ℝ) ≤ (n : ℝ) := by exact_mod_cast hden
    linarith
  have hden2 : 2 ≤ r.den := by
    rcases Nat.lt_or_ge r.den 2 with h | h
    · exfalso
      have hq1 : r.den = 1 := by have := r.pos; omega
      apply hmaj
      have hnum : (r : ℝ) = (r.num : ℝ) := by
        rw [← hrr, hq1]
        norm_num
      refine ⟨hα, (r.num : ℚ), ?_, ?_⟩
      · rw [Rat.den_intCast]
        have h : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
          Real.one_le_rpow hN1 (by norm_num)
        simpa using h
      · rw [Rat.den_intCast, Nat.cast_one, one_mul, Rat.cast_intCast, ← hnum]
        refine hbd.trans ?_
        apply one_div_le_one_div_of_le hτpos
        rw [hq1, Nat.cast_one, mul_one]
        linarith
    · exact h
  refine ⟨r.den, r.num, hden2, hdenle, ?_, hclose⟩
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hdvdAbs : r.den ∣ r.num.natAbs := by
    refine ⟨t.natAbs, ?_⟩
    rw [ht, Int.natAbs_mul, Int.natAbs_natCast]
  have hcop : r.num.natAbs.Coprime r.den := r.reduced
  have hone := Nat.eq_one_of_dvd_coprimes hcop hdvdAbs (dvd_refl r.den)
  omega

/-! ## Step 2: a short interval costs only `O(log τ)` of reciprocal weight

For one interval `[l, u]` of length at most `1/τ^2` take every fraction `a/q` with
`2 ≤ q ≤ ⌊τ⌋` whose value lies in `[l - 1/τ, u + 1/τ]`. Dirichlet at level `⌊τ⌋` puts every
point of the interval inside one of the corresponding arcs, and row by row the numerators in
that window number at most `(u - l + 2/τ) q + 1`, so the total reciprocal weight is at most
`3 + (1 + log τ)`. -/

private lemma int_card_Icc_le {a b : ℤ} (h : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
  have hc := Int.card_Icc_of_le (a := a) (b := b) (show a ≤ b + 1 by omega)
  have hcast : ((Finset.Icc a b).card : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by
    exact_mod_cast hc
  rw [hcast]
  push_cast
  linarith

private lemma nat_card_Icc_le {a b : ℕ} (h : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
  have hc : (Finset.Icc a b).card = b + 1 - a := Nat.card_Icc a b
  have hcast : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    rw [Nat.cast_sub (by omega : a ≤ b + 1)]
    push_cast
    ring
  rw [hc, hcast]
  linarith

private lemma sum_biUnion_le_of_nonneg {ι β : Type*} [DecidableEq β] {s : Finset ι}
    {t : ι → Finset β} {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  have hpoint : ∀ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, (if x ∈ t a then f x else 0) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    have hterm : (if x ∈ t a then f x else 0) = f x := if_pos hxa
    have hnonneg : ∀ b ∈ s, 0 ≤ (if x ∈ t b then f x else 0) := by
      intro b _
      split_ifs with h
      · exact hf x
      · exact le_refl 0
    have hsingle := Finset.single_le_sum (f := fun b => if x ∈ t b then f x else 0) hnonneg ha
    rwa [hterm] at hsingle
  calc ∑ x ∈ s.biUnion t, f x
      ≤ ∑ x ∈ s.biUnion t, ∑ a ∈ s, (if x ∈ t a then f x else 0) := Finset.sum_le_sum hpoint
    _ = ∑ a ∈ s, ∑ x ∈ s.biUnion t, (if x ∈ t a then f x else 0) := Finset.sum_comm
    _ ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => hf x)

set_option maxHeartbeats 1000000 in
private theorem arc_cover_interval357 (N : ℕ) (hN : 1 ≤ N)
    (hτ2 : 2 ≤ (N : ℝ) ^ (1 / 7 : ℝ)) {l u : ℝ}
    (hlen : u - l ≤ 1 / ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2) :
    ∃ F : Finset (ℕ × ℤ),
      (∀ p ∈ F, 2 ≤ p.1) ∧ (∀ p ∈ F, ¬ ((p.1 : ℤ) ∣ p.2)) ∧
      (∀ p ∈ F, (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
      (∀ α ∈ Set.Icc l u, α ∈ Set.Icc (0 : ℝ) 1 → α ∉ majorArcs280 N →
        ∃ p ∈ F, |α - (p.2 : ℝ) / (p.1 : ℝ)| ≤
          1 / ((p.1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ∧
      (∑ p ∈ F, 1 / (p.1 : ℝ)) ≤ 5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ)) := by
  classical
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hτ1 : 1 ≤ τ := le_trans (by norm_num) hτ2
  by_cases hlu : l ≤ u
  · set Q : ℕ := ⌊τ⌋₊ with hQdef
    have hQle : (Q : ℝ) ≤ τ := by rw [hQdef]; exact Nat.floor_le hτpos.le
    have hQ2 : 2 ≤ Q := by rw [hQdef]; exact Nat.le_floor hτ2
    set aLo : ℕ → ℤ := fun q => ⌈(l - 1 / τ) * (q : ℝ)⌉ with haLo
    set aHi : ℕ → ℤ := fun q => ⌊(u + 1 / τ) * (q : ℝ)⌋ with haHi
    set A : ℕ → Finset (ℕ × ℤ) := fun q =>
      ((Finset.Icc (aLo q) (aHi q)).filter (fun a => ¬ ((q : ℤ) ∣ a))).image (fun a => (q, a))
      with hA
    refine ⟨(Finset.Icc 2 Q).biUnion A, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.mp hp
      rw [hA] at hpq
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hpq
      exact (Finset.mem_Icc.mp hq).1
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.mp hp
      rw [hA] at hpq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpq
      exact (Finset.mem_filter.mp ha).2
    · intro p hp
      obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.mp hp
      rw [hA] at hpq
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hpq
      exact le_trans (by exact_mod_cast (Finset.mem_Icc.mp hq).2) hQle
    · -- every point of the interval lands in one of the arcs
      intro α hα hα01 hmaj
      obtain ⟨q, a, hq2, hqle, hndvd, hclose⟩ := rat_arc_cover357 N hN hα01 hmaj
      obtain ⟨hαl, hαu⟩ := hα
      have hqpos : (0 : ℝ) < (q : ℝ) := by
        have : (0 : ℕ) < q := by omega
        exact_mod_cast this
      have hqQ : q ≤ Q := by rw [hQdef]; exact Nat.le_floor hqle
      have hinvq : 1 / ((q : ℝ) * τ) ≤ 1 / τ := by
        apply one_div_le_one_div_of_le hτpos
        calc τ = 1 * τ := by ring
          _ ≤ (q : ℝ) * τ := by
              refine mul_le_mul_of_nonneg_right ?_ hτpos.le
              exact_mod_cast (show 1 ≤ q by omega)
      have hcloseτ : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * τ) := by
        simpa [hτdef] using hclose
      have hmid_l : l - 1 / τ ≤ α - 1 / ((q : ℝ) * τ) := by linarith [hαl, hinvq]
      have hmid_u : α + 1 / ((q : ℝ) * τ) ≤ u + 1 / τ := by linarith [hαu, hinvq]
      have hlow : l - 1 / τ ≤ (a : ℝ) / (q : ℝ) := by
        have h2 : α - (a : ℝ) / (q : ℝ) ≤ 1 / ((q : ℝ) * τ) := (abs_le.mp hcloseτ).2
        linarith [h2, hmid_l]
      have hhigh : (a : ℝ) / (q : ℝ) ≤ u + 1 / τ := by
        have h1 : -(1 / ((q : ℝ) * τ)) ≤ α - (a : ℝ) / (q : ℝ) := (abs_le.mp hcloseτ).1
        linarith [h1, hmid_u]
      have haLow : (l - 1 / τ) * (q : ℝ) ≤ (a : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_right hlow hqpos.le
        rwa [div_mul_cancel₀ _ hqpos.ne'] at h1
      have haHigh : (a : ℝ) ≤ (u + 1 / τ) * (q : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_right hhigh hqpos.le
        rwa [div_mul_cancel₀ _ hqpos.ne'] at h1
      have hamem : a ∈ (Finset.Icc (aLo q) (aHi q)).filter (fun a => ¬ ((q : ℤ) ∣ a)) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hndvd⟩
        · rw [haLo]; exact Int.ceil_le.mpr haLow
        · rw [haHi]; exact Int.le_floor.mpr haHigh
      refine ⟨(q, a), ?_, hclose⟩
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_Icc.mpr ⟨hq2, hqQ⟩, Finset.mem_image.mpr ⟨a, hamem, rfl⟩⟩
    · -- the reciprocal weight
      have hlenτ : u - l ≤ 1 / τ := by
        refine hlen.trans ?_
        apply one_div_le_one_div_of_le hτpos
        nlinarith [hτpos, hτ1]

      have hrow : ∀ q ∈ Finset.Icc 2 Q,
          (∑ p ∈ A q, 1 / (p.1 : ℝ)) ≤ (u - l + 2 / τ) + 1 / (q : ℝ) := by
        intro q hq
        have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
        have hqpos : (0 : ℝ) < (q : ℝ) := by
          have : (0 : ℕ) < q := by omega
          exact_mod_cast this
        have hsumA : (∑ p ∈ A q, 1 / (p.1 : ℝ)) = ((A q).card : ℝ) * (1 / (q : ℝ)) := by
          have hconst : ∀ p ∈ A q, 1 / (p.1 : ℝ) = 1 / (q : ℝ) := by
            intro p hp
            rw [hA] at hp
            obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
            rfl
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
        rw [hsumA]
        have hcardA : ((A q).card : ℝ) ≤ (u - l + 2 / τ) * (q : ℝ) + 1 := by
          have hle0 : (A q).card ≤ (Finset.Icc (aLo q) (aHi q)).card := by
            rw [hA]
            exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
          have h1 : ((A q).card : ℝ) ≤ ((Finset.Icc (aLo q) (aHi q)).card : ℝ) := by
            exact_mod_cast hle0
          by_cases hle : aLo q ≤ aHi q
          · have h2 : ((Finset.Icc (aLo q) (aHi q)).card : ℝ) ≤
                ((aHi q : ℤ) : ℝ) - ((aLo q : ℤ) : ℝ) + 1 := int_card_Icc_le hle
            have hfloor : ((aHi q : ℤ) : ℝ) ≤ (u + 1 / τ) * (q : ℝ) := by
              rw [haHi]; exact Int.floor_le _
            have hceil : (l - 1 / τ) * (q : ℝ) ≤ ((aLo q : ℤ) : ℝ) := by
              rw [haLo]; exact Int.le_ceil _
            have halg : (u + 1 / τ) * (q : ℝ) - (l - 1 / τ) * (q : ℝ) =
                (u - l + 2 / τ) * (q : ℝ) := by ring
            linarith
          · have hempty : Finset.Icc (aLo q) (aHi q) = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro a ha
              have h1 := Finset.mem_Icc.mp ha
              omega
            have hz : (A q).card = 0 := by
              rw [hA]
              simp [hempty]
            rw [hz]
            simp only [Nat.cast_zero]
            have h0 : 0 ≤ u - l := by linarith
            have hA0 : (0 : ℝ) ≤ u - l + 2 / τ := by
              have : (0 : ℝ) < 2 / τ := by positivity
              linarith
            have := mul_nonneg hA0 hqpos.le
            linarith
        calc ((A q).card : ℝ) * (1 / (q : ℝ))
            ≤ ((u - l + 2 / τ) * (q : ℝ) + 1) * (1 / (q : ℝ)) :=
              mul_le_mul_of_nonneg_right hcardA (by positivity)
          _ = (u - l + 2 / τ) + 1 / (q : ℝ) := by
              field_simp
              try ring
      have hharm : (harmonic Q : ℝ) = ∑ i ∈ Finset.Icc 1 Q, 1 / (i : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [one_div]
      have hle1 : (∑ q ∈ Finset.Icc 2 Q, 1 / (q : ℝ)) ≤ (harmonic Q : ℝ) := by
        rw [hharm]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by norm_num) le_rfl) ?_
        intro i _ _
        positivity
      have hle2 : (harmonic Q : ℝ) ≤ 1 + Real.log τ := by
        refine (harmonic_le_one_add_log Q).trans ?_
        have hQpos : (0 : ℝ) < (Q : ℝ) := by
          have : (0 : ℕ) < Q := by omega
          exact_mod_cast this
        have := Real.log_le_log hQpos hQle
        linarith
      have hcardQ : ((Finset.Icc 2 Q).card : ℝ) ≤ (Q : ℝ) := by
        have h1 : ((Finset.Icc 2 Q).card : ℝ) ≤ (Q : ℝ) - ((2 : ℕ) : ℝ) + 1 :=
          nat_card_Icc_le (a := 2) (b := Q) hQ2
        have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
        linarith
      have hstep : (u - l + 2 / τ) ≤ 3 / τ := by
        have h3 : 2 / τ + 1 / τ = 3 / τ := by ring
        linarith
      have hcoef : (0 : ℝ) ≤ u - l + 2 / τ := by
        have h0 : 0 ≤ u - l := by linarith
        have h1 : (0 : ℝ) < 2 / τ := by positivity
        linarith
      calc (∑ p ∈ (Finset.Icc 2 Q).biUnion A, 1 / (p.1 : ℝ))
          ≤ ∑ q ∈ Finset.Icc 2 Q, ∑ p ∈ A q, 1 / (p.1 : ℝ) :=
            sum_biUnion_le_of_nonneg (fun x => by positivity)
        _ ≤ ∑ q ∈ Finset.Icc 2 Q, ((u - l + 2 / τ) + 1 / (q : ℝ)) :=
            Finset.sum_le_sum hrow
        _ = ((Finset.Icc 2 Q).card : ℝ) * (u - l + 2 / τ) +
              ∑ q ∈ Finset.Icc 2 Q, 1 / (q : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Q : ℝ) * (3 / τ) + (1 + Real.log τ) := by
            have h1 : ((Finset.Icc 2 Q).card : ℝ) * (u - l + 2 / τ) ≤
                (Q : ℝ) * (u - l + 2 / τ) :=
              mul_le_mul_of_nonneg_right hcardQ hcoef
            have h2 : (Q : ℝ) * (u - l + 2 / τ) ≤ (Q : ℝ) * (3 / τ) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
            linarith [hle1.trans hle2]
        _ ≤ 5 + 2 * Real.log τ := by
            have hQ3 : (Q : ℝ) * (3 / τ) ≤ 3 := by
              have h1 : (Q : ℝ) * (3 / τ) ≤ τ * (3 / τ) :=
                mul_le_mul_of_nonneg_right hQle (by positivity)
              have h2 : τ * (3 / τ) = 3 := by field_simp
              linarith
            have hlog : 0 ≤ Real.log τ := Real.log_nonneg hτ1
            linarith
  · -- the interval is empty
    refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · intro α hα
      exfalso
      obtain ⟨h1, h2⟩ := hα
      linarith
    · simp only [Finset.sum_empty]
      have hlog : 0 ≤ Real.log τ := Real.log_nonneg hτ1
      linarith

/-! ## Step 3: the leaf follows from the interval cover alone -/

set_option maxHeartbeats 1000000 in
/-- `exceptional_cover357` from the P0093 Lemma 5 interval cover of the large-value set. -/
theorem exceptional_cover357_of_intervals
    (hint : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ I : Finset (ℝ × ℝ),
        (I.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ p ∈ I, p.2 - p.1 ≤ 1 / ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2) ∧
        {α : ℝ | α ∈ Set.Icc 0 1 ∧
          (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ⊆
          ⋃ p ∈ I, Set.Icc p.1 p.2) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∃ F : Finset (ℕ × ℤ),
        (∀ p ∈ F, 1 ≤ p.1) ∧ (∀ p ∈ F, ¬ ((p.1 : ℤ) ∣ p.2)) ∧
        (∀ p ∈ F, (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        (∀ α ∈ exceptionalArcs280 N η, ∃ p ∈ F,
          |α - (p.2 : ℝ) / (p.1 : ℝ)| ≤
            1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) ∧
        (∑ p ∈ F, 1 / (p.1 : ℝ)) ≤ (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) := by
  classical
  obtain ⟨η, hη0, hη1, A, hA, N0, hI⟩ := hint
  have hexp : (13 / 140 : ℝ) = 1 / 7 - 1 / 20 := by norm_num
  -- the logarithm is absorbed by the saving
  have hlogbound : ∀ N : ℕ, 1 ≤ N → Real.log (N : ℝ) ≤ 560 * (N : ℝ) ^ (1 / 560 : ℝ) := by
    intro N hN1'
    have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have h := Real.log_le_rpow_div (ε := (1 / 560 : ℝ)) hpos.le (by norm_num)
    rwa [show (N : ℝ) ^ (1 / 560 : ℝ) / (1 / 560 : ℝ) = 560 * (N : ℝ) ^ (1 / 560 : ℝ) by
      field_simp] at h
  have hevent : ∀ᶠ N : ℕ in atTop, 165 * A ≤ (N : ℝ) ^ (227 / 2800 : ℝ) := by
    have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (227 / 2800 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 227 / 2800)).comp
        tendsto_natCast_atTop_atTop
    exact htend.eventually (eventually_ge_atTop (165 * A))
  rw [eventually_atTop] at hevent
  obtain ⟨N1, hN1⟩ := hevent
  refine ⟨η, hη0, hη1, max N0 (max N1 128), ?_⟩
  intro N hN
  have hN0lt : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1le : N1 ≤ N :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left N1 128) (le_max_right N0 (max N1 128))) hN)
  have hN128 : 128 ≤ N :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right N1 128) (le_max_right N0 (max N1 128))) hN)
  have hNge1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hτ2 : 2 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    have h1 : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
      have h128 : (128 : ℝ) = 2 ^ 7 := by norm_num
      rw [h128, ← Real.rpow_natCast (2 : ℝ) 7, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN128) (by norm_num)
  obtain ⟨I, hcard, hlen, hcover⟩ := hI N hN0lt
  have hex : ∀ p : {p // p ∈ I}, ∃ G : Finset (ℕ × ℤ),
      (∀ x ∈ G, 2 ≤ x.1) ∧ (∀ x ∈ G, ¬ ((x.1 : ℤ) ∣ x.2)) ∧
      (∀ x ∈ G, (x.1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
      (∀ α ∈ Set.Icc p.val.1 p.val.2, α ∈ Set.Icc (0 : ℝ) 1 → α ∉ majorArcs280 N →
        ∃ x ∈ G, |α - (x.2 : ℝ) / (x.1 : ℝ)| ≤
          1 / ((x.1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ∧
      (∑ x ∈ G, 1 / (x.1 : ℝ)) ≤ 5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ)) :=
    fun p => arc_cover_interval357 N hNge1 hτ2 (hlen p.val p.property)
  choose G hG using hex
  refine ⟨I.attach.biUnion G, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, -, hpx⟩ := Finset.mem_biUnion.mp hx
    exact le_trans (by norm_num) ((hG p).1 x hpx)
  · intro x hx
    obtain ⟨p, -, hpx⟩ := Finset.mem_biUnion.mp hx
    exact (hG p).2.1 x hpx
  · intro x hx
    obtain ⟨p, -, hpx⟩ := Finset.mem_biUnion.mp hx
    exact (hG p).2.2.1 x hpx
  · -- the cover of the exceptional set
    intro α hα
    have hlarge : α ∈ {α : ℝ | α ∈ Set.Icc 0 1 ∧
        (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} := ⟨hα.1, hα.2.2⟩
    obtain ⟨p, hp, hαp⟩ := Set.mem_iUnion₂.mp (hcover hlarge)
    obtain ⟨x, hxG, hxarc⟩ := (hG ⟨p, hp⟩).2.2.2.1 α hαp hα.1 hα.2.1
    exact ⟨x, Finset.mem_biUnion.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, hxG⟩, hxarc⟩
  · -- the weight
    have hlogτ : (0 : ℝ) ≤ Real.log ((N : ℝ) ^ (1 / 7 : ℝ)) :=
      Real.log_nonneg (Real.one_le_rpow (by exact_mod_cast hNge1) (by norm_num))
    have hstep : A * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) ≤
        (N : ℝ) ^ (13 / 140 - 1 / 100 : ℝ) := by
      have hlogN : Real.log (N : ℝ) ≤ 560 * (N : ℝ) ^ (1 / 560 : ℝ) := hlogbound N hNge1
      have hlogτ' : Real.log ((N : ℝ) ^ (1 / 7 : ℝ)) = (1 / 7) * Real.log (N : ℝ) :=
        Real.log_rpow hNpos _
      have hpow1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 560 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast hNge1) (by norm_num)
      have hpowpos : (0 : ℝ) < (N : ℝ) ^ (1 / 560 : ℝ) := by positivity
      have hfr : 5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ)) ≤ 165 * (N : ℝ) ^ (1 / 560 : ℝ) := by
        rw [hlogτ']
        nlinarith
      calc A * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ)))
          ≤ A * (165 * (N : ℝ) ^ (1 / 560 : ℝ)) := mul_le_mul_of_nonneg_left hfr hA.le
        _ = 165 * A * (N : ℝ) ^ (1 / 560 : ℝ) := by ring
        _ ≤ (N : ℝ) ^ (227 / 2800 : ℝ) * (N : ℝ) ^ (1 / 560 : ℝ) :=
            mul_le_mul_of_nonneg_right (hN1 N hN1le) hpowpos.le
        _ = (N : ℝ) ^ (227 / 2800 + 1 / 560 : ℝ) := by rw [← Real.rpow_add hNpos]
        _ = (N : ℝ) ^ (13 / 140 - 1 / 100 : ℝ) := by norm_num
    calc (∑ x ∈ I.attach.biUnion G, 1 / (x.1 : ℝ))
        ≤ ∑ p ∈ I.attach, ∑ x ∈ G p, 1 / (x.1 : ℝ) :=
          sum_biUnion_le_of_nonneg (fun x => by positivity)
      _ ≤ ∑ p ∈ I.attach, (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) :=
          Finset.sum_le_sum (fun p _ => (hG p).2.2.2.2)
      _ = (I.attach.card : ℝ) * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (I.card : ℝ) * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) := by
          rw [Finset.card_attach]
      _ ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
      _ = A * (5 + 2 * Real.log ((N : ℝ) ^ (1 / 7 : ℝ))) * (N : ℝ) ^ (1 / 100 : ℝ) := by ring
      _ ≤ (N : ℝ) ^ (13 / 140 - 1 / 100 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (N : ℝ) ^ (13 / 140 : ℝ) := by
          rw [← Real.rpow_add hNpos]
          norm_num
      _ = (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) := by rw [hexp]


/-- LEAF. Step 1 of the exceptional set analysis: the rational arc cover and its
weight. For one absolute positive threshold, every point of the exceptional set
lies on a short arc around a rational written in lowest terms, whose denominator
is at most N to the one seventh and whose half width is the reciprocal of that
denominator times N to the one seventh. The covering rationals carry total
reciprocal weight that gains the power saving one twentieth over the trivial
weight N to the one seventh of all rationals of that size. This is the covering
and counting input only: it carries no integral and no hypothesis. -/
theorem exceptional_cover357 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∃ F : Finset (ℕ × ℤ),
        (∀ p ∈ F, 1 ≤ p.1) ∧
        (∀ p ∈ F, ¬ ((p.1 : ℤ) ∣ p.2)) ∧
        (∀ p ∈ F, (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        (∀ α ∈ exceptionalArcs280 N η, ∃ p ∈ F,
          |α - (p.2 : ℝ) / (p.1 : ℝ)| ≤
            1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) ∧
        (∑ p ∈ F, 1 / (p.1 : ℝ)) ≤ (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) :=
  exceptional_cover357_of_intervals large_value_intervals435

/-- LEAF. Step 2 of the exceptional set analysis: the mass of the primes on one
short arc. At a rational with denominator one at most q not dividing the
numerator, the square mean of the damped prime series over the arc of half width
the reciprocal of q times N to the one seventh is at most a constant times N
divided by both q and N to the one seventh, with a fixed power of the logarithm
of N. This is one arc only, not the whole exceptional set, and it excludes the
principal arcs where the mean is of size N. -/
theorem local_prime_mass357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
          (∫ α in Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
              ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
            ‖primeFourier111 N α‖ ^ 2) ≤
          B * (N : ℝ) / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13 := by
  sorry

/-- The measure theory core: for a nonnegative continuous `f`, the mass over a set covered by
finitely many closed arcs is at most the sum of the masses of the arcs. -/
private theorem cover_sum_bound_wip (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (hs : MeasurableSet s) (hsb : s ⊆ Set.Icc 0 1)
    (F : Finset (ℕ × ℤ)) (lo hi : ℕ × ℤ → ℝ)
    (hsub : s ⊆ ⋃ p ∈ F, Set.Icc (lo p) (hi p)) :
    (∫ x in s, f x) ≤ ∑ p ∈ F, ∫ x in Set.Icc (lo p) (hi p), f x := by
  have hpoint : ∀ x : ℝ, s.indicator f x ≤ ∑ p ∈ F, (Set.Icc (lo p) (hi p)).indicator f x := by
    intro x
    by_cases hx : x ∈ s
    · have hex : ∃ p ∈ F, x ∈ Set.Icc (lo p) (hi p) := by
        simpa only [Set.mem_iUnion, exists_prop] using hsub hx
      obtain ⟨p, hpF, hpI⟩ := hex
      have hnonneg : ∀ q ∈ F, 0 ≤ (Set.Icc (lo q) (hi q)).indicator f x := by
        intro q _
        by_cases h : x ∈ Set.Icc (lo q) (hi q)
        · rw [Set.indicator_of_mem h]; exact hfn x
        · rw [Set.indicator_of_notMem h]
      have hsingle := Finset.single_le_sum
        (f := fun q => (Set.Icc (lo q) (hi q)).indicator f x) hnonneg hpF
      rw [Set.indicator_of_mem hpI] at hsingle
      rw [Set.indicator_of_mem hx]
      exact hsingle
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun q _ => by
        by_cases h : x ∈ Set.Icc (lo q) (hi q)
        · rw [Set.indicator_of_mem h]; exact hfn x
        · rw [Set.indicator_of_notMem h])
  have hIntS : Integrable (s.indicator f) := by
    rw [integrable_indicator_iff hs]
    exact hf.integrableOn_Icc.mono_set hsb
  have hIntP : ∀ p ∈ F, Integrable ((Set.Icc (lo p) (hi p)).indicator f) := by
    intro p _
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hf.integrableOn_Icc
  have hIntSum : Integrable (fun x => ∑ p ∈ F, (Set.Icc (lo p) (hi p)).indicator f x) :=
    integrable_finsetSum F hIntP
  have hmono := integral_mono hIntS hIntSum hpoint
  rw [integral_indicator hs, integral_finset_sum F hIntP] at hmono
  refine hmono.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun p _ => integral_indicator measurableSet_Icc)

/-- LEAF. Step 3 of the exceptional set analysis: the finite cover sum. The square
mean of the prime series over a set contained in the union of finitely many closed
arcs is at most the sum over those arcs of the square mean on the arc, so a
per-arc estimate turns into an estimate for the whole exceptional set with the
reciprocal denominators factored out. This is subadditivity of the integral over a
finite cover; it contains no arithmetic and no hypothesis. -/
theorem cover_mass_summation357 (N : ℕ) (η : ℝ) (F : Finset (ℕ × ℤ)) (B : ℝ)
    (hB : 0 ≤ B)
    (hq : ∀ p ∈ F, 1 ≤ p.1)
    (hcover : exceptionalArcs280 N η ⊆
      ⋃ p ∈ F, Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))))
    (harc : ∀ p ∈ F,
      (∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
          ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
        ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13) :
    (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
        (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
  by_cases hN1 : 1 ≤ N
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h0 : (0 : ℝ) < (N : ℕ) := by exact_mod_cast (by omega : 0 < N)
      exact_mod_cast h0
    have hcont : Continuous (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) :=
      (continuous_prime_fourier111 N hN1).norm.pow 2
    have hbound := cover_sum_bound_wip (fun α => ‖primeFourier111 N α‖ ^ 2) hcont
      (fun α => by positivity) (exceptionalArcs280 N η)
      (measurable_exceptional357 N hN1 η) (fun α hα => hα.1) F
      (fun p => (p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
      (fun p => (p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
      hcover
    have hsum : (∑ p ∈ F,
        ∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
          ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖primeFourier111 N α‖ ^ 2) ≤
        ∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) *
          Real.log (N : ℝ) ^ 13 :=
      Finset.sum_le_sum (fun p hp => harc p hp)
    have halg : (∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) *
        Real.log (N : ℝ) ^ 13) =
        B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
          (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hq1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hq p hp
      have hppos : (0 : ℝ) < (p.1 : ℝ) := by linarith
      have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
      have hsubr : (N : ℝ) ^ (1 - (1 / 7 : ℝ)) = (N : ℝ) / ((N : ℝ) ^ (1 / 7 : ℝ)) := by
        rw [Real.rpow_sub hNpos, Real.rpow_one]
      rw [hsubr]
      field_simp
      try ring
    exact hbound.trans (hsum.trans (le_of_eq halg))
  · -- the degenerate case N = 0
    have hN0 : N = 0 := by omega
    subst hN0
    have hexp1 : ∀ m : ℕ,
        Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) = 1 := by
      intro m
      have hden : (-(((2 ^ (m + 1) : ℕ) : ℝ))) / ((0 : ℕ) : ℝ) = 0 := by simp
      rw [hden, Real.exp_zero]
    have hzero : ∀ α : ℝ, powerFourier111 0 α = 0 := by
      intro α
      have hnot : ¬ Summable (fun m : ℕ =>
          (Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
        intro h
        have h2 : Tendsto (fun m : ℕ =>
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖)
            atTop (𝓝 0) := by
          simpa using h.tendsto_atTop_zero.norm
        have hterm : ∀ m : ℕ,
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖ = 1 := by
          intro m
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hexp1 m]
          simp
        have h3 : Tendsto (fun m : ℕ =>
            ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖)
            atTop (𝓝 1) := by
          have hconst : (fun m : ℕ =>
              ‖(Real.exp (-(((2 ^ (m + 1) : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) : ℝ) * Complex.I)‖) =
              fun _ => (1 : ℝ) := funext hterm
          rw [hconst]
          exact tendsto_const_nhds
        have h01 := tendsto_nhds_unique h2 h3
        norm_num at h01
      unfold powerFourier111
      exact tsum_eq_zero_of_not_summable hnot
    have hempty : exceptionalArcs280 0 η = ∅ := by
      have hsub0 : exceptionalArcs280 0 η ⊆ ∅ := by
        intro α hα
        have h2 := hα.2.2
        rw [hzero 0, hzero α, norm_zero, mul_zero] at h2
        exact absurd h2 (lt_irrefl 0)
      exact Set.Subset.antisymm hsub0 (Set.empty_subset _)
    have hrhs : B * ((0 : ℕ) : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log ((0 : ℕ) : ℝ) ^ 13 *
        (∑ p ∈ F, 1 / (p.1 : ℝ)) = 0 := by
      norm_num [Real.zero_rpow, Real.log_zero]
    rw [hempty, hrhs]
    simp

/-- LEAF. Step 4 of the exceptional set analysis: the logarithm is absorbed by the
saving. Beyond some point a fixed power of the logarithm of N is at most N to the
one fortieth, which is what the cover weight leaves free. This is one elementary
numeric inequality about the real logarithm and a real power. -/
theorem log_power_absorption357 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log (N : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
  refine ⟨560 ^ 7280, ?_⟩
  intro N hN
  have hNge : 560 ^ 7280 ≤ N := le_of_lt hN
  have hpos : 0 < 560 ^ 7280 := by positivity
  have hN1n : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1n
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : Real.log (N : ℝ) ≤ 560 * (N : ℝ) ^ (1 / 560 : ℝ) := by
    have h := Real.log_le_rpow_div (x := (N : ℝ)) (ε := (1 / 560 : ℝ)) hNpos.le
      (by norm_num)
    rwa [show (N : ℝ) ^ (1 / 560 : ℝ) / (1 / 560 : ℝ) = 560 * (N : ℝ) ^ (1 / 560 : ℝ) by
      field_simp] at h
  have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have h13 : Real.log (N : ℝ) ^ 13 ≤ (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 :=
    pow_le_pow_left₀ hlog0 hlog 13
  have hexp : (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 =
      (560 : ℝ) ^ 13 * (N : ℝ) ^ (13 / 560 : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 560 : ℝ)) 13,
      ← Real.rpow_mul (le_of_lt hNpos),
      show ((1 / 560 : ℝ) * ((13 : ℕ) : ℝ)) = (13 / 560 : ℝ) by norm_num]
  have hNbig : (560 : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 560 : ℝ) := by
    have h7280 : (560 : ℝ) ^ 7280 ≤ (N : ℝ) := by
      calc (560 : ℝ) ^ 7280 = ((560 ^ 7280 : ℕ) : ℝ) := by push_cast; norm_num
        _ ≤ (N : ℝ) := by exact_mod_cast hNge
    calc (560 : ℝ) ^ 13 = ((560 : ℝ) ^ 7280) ^ (1 / 560 : ℝ) := by
          rw [← Real.rpow_natCast (560 : ℝ) 7280,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 560),
            show (((7280 : ℕ) : ℝ) * (1 / 560 : ℝ)) = ((13 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
      _ ≤ (N : ℝ) ^ (1 / 560 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h7280 (by norm_num)
  calc Real.log (N : ℝ) ^ 13 ≤ (560 * (N : ℝ) ^ (1 / 560 : ℝ)) ^ 13 := h13
    _ = (560 : ℝ) ^ 13 * (N : ℝ) ^ (13 / 560 : ℝ) := hexp
    _ ≤ (N : ℝ) ^ (1 / 560 : ℝ) * (N : ℝ) ^ (13 / 560 : ℝ) :=
        mul_le_mul_of_nonneg_right hNbig (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num

/-- The target assembled from the four leaves above. -/
theorem exceptional_prime_mass357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨η, hη0, hη1, Nc, hcov⟩ := exceptional_cover357
  obtain ⟨B, hB0, NB, hmass⟩ := local_prime_mass357 hG
  obtain ⟨NL, hlog⟩ := log_power_absorption357
  refine ⟨η, hη0, hη1, B, hB0, max Nc (max NB NL), ?_⟩
  intro N hN
  have hNc : Nc < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNB : NB < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNL : NL < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos_nat : 0 < N := lt_of_le_of_lt (Nat.zero_le NL) hNL
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : 1 ≤ N := hNpos_nat
    exact_mod_cast h
  obtain ⟨F, hq, hred, hqle, hcovF, hweight⟩ := hcov N hNc
  have hsub : exceptionalArcs280 N η ⊆
      ⋃ p ∈ F, Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))) := by
    intro α hα
    obtain ⟨p, hpF, hp⟩ := hcovF α hα
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨p, hpF, ?_⟩
    simp only [Set.mem_Icc]
    have h1 := (abs_le.mp hp).1
    have h2 := (abs_le.mp hp).2
    constructor <;> linarith
  have harc : ∀ p ∈ F,
      (∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖primeFourier111 N α‖ ^ 2) ≤
        B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13 := by
    intro p hp
    exact hmass N hNB p.1 (hq p hp) (hqle p hp) p.2 (hred p hp)
  have hsum := cover_mass_summation357 N η F B hB0.le hq hsub harc
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hcoef : 0 ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 :=
    mul_nonneg (mul_nonneg hB0.le (Real.rpow_nonneg hNpos.le _)) (pow_nonneg hlogN 13)
  have hkey1 : (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) =
      (N : ℝ) ^ (1 - (1 / 20 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hkey2 : (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) =
      (N : ℝ) ^ (1 - (1 / 40 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  calc
    (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2)
        ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
            (∑ p ∈ F, 1 / (p.1 : ℝ)) := hsum
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
          (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hweight hcoef
    _ = B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * Real.log (N : ℝ) ^ 13 := by
      rw [show B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
            (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ) =
          B * ((N : ℝ) ^ (1 - (1 / 7 : ℝ)) * (N : ℝ) ^ (1 / 7 - 1 / 20 : ℝ)) *
            Real.log (N : ℝ) ^ 13 from by ring,
        hkey1]
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) :=
      mul_le_mul_of_nonneg_left (hlog N hNL)
        (mul_nonneg hB0.le (Real.rpow_nonneg hNpos.le _))
    _ = B * (N : ℝ) ^ (1 - (1 / 40 : ℝ)) := by
      rw [show B * (N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ) =
          B * ((N : ℝ) ^ (1 - (1 / 20 : ℝ)) * (N : ℝ) ^ (1 / 40 : ℝ)) from by ring,
        hkey2]
    _ ≤ B * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hB0.le
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

end LeanLab.Linnik1951
