/-
Integral glue for PP1993 page 46 display 14 and page 47 display 15.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Only the finite Farey cover remains OPEN in this module.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.LocalData489

namespace LeanLab.Languasco2004.RationalGlue489
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp413b Decomp489b
noncomputable section
/-! ### Private support lemmas for the finite Farey cover -/

private lemma mem_farey_pair {N : ℕ} {p : ℕ × ℕ} :
    p ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun r : ℕ × ℕ => r.1 ≤ r.2 ∧ Nat.Coprime r.1 r.2)) ↔
      (1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2) := by
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  tauto

/-- Two overlapping boxes about `p ≤ p'` cover a segment reaching past both ends. -/
private theorem segment_two_box {p r p' r' L U : ℝ}
    (h1 : p - r ≤ L) (h2 : U ≤ p' + r') (hgap : p' - p ≤ r + r') :
    Set.Icc L U ⊆ Set.Icc (p - r) (p + r) ∪ Set.Icc (p' - r') (p' + r') := by
  rintro α ⟨hαL, hαU⟩
  rcases le_total α p with h | h
  · exact Or.inl ⟨by linarith, by linarith⟩
  rcases le_total p' α with h' | h'
  · exact Or.inr ⟨by linarith, by linarith⟩
  by_cases hc : α ≤ p + r
  · exact Or.inl ⟨by linarith, hc⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- Dirichlet approximation in the integer shape used below. -/
private theorem dyadic_approx (N : ℕ) (hN0 : 0 < N) {m : ℝ}
    (hmN : 1/(N:ℝ) ≤ m) (hm1 : m ≤ 1) :
    ∃ u v : ℕ, 1 ≤ u ∧ u ≤ v ∧ v ≤ N ∧ Nat.Coprime u v ∧
      |m - (u:ℝ)/(v:ℝ)| ≤ 1/(((N:ℝ)+1)*(v:ℝ)) := by
  obtain ⟨q, hq, hqN⟩ := Real.exists_rat_abs_sub_le_and_den_le m hN0
  have hden : 0 < q.den := q.den_pos
  have hdenR : (0:ℝ) < (q.den:ℝ) := by exact_mod_cast hden
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN0
  have hq' : |m - (q:ℝ)| ≤ 1/(((N:ℝ)+1)*(q.den:ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hq
  have hcast : (q:ℝ) = (q.num:ℝ)/(q.den:ℝ) := by
    have h := congrArg (fun r : ℚ => (r:ℝ)) (Rat.num_div_den q)
    simpa using h.symm
  have hNinv : (0:ℝ) < 1/(N:ℝ) := by positivity
  have hdeninv : (0:ℝ) < 1/(q.den:ℝ) := by positivity
  have hqpos : 0 < q := by
    by_cases hle : q ≤ 0
    · exfalso
      have hqR : (q:ℝ) ≤ 0 := by exact_mod_cast hle
      have habs : |m - (q:ℝ)| = m - (q:ℝ) := abs_of_nonneg (by linarith [hNinv])
      have hd1 : (1:ℝ) ≤ (q.den:ℝ) := by exact_mod_cast hden
      have h3 : 1/(((N:ℝ)+1)*(q.den:ℝ)) < 1/(N:ℝ) := by
        rw [div_lt_div_iff₀ (by positivity) hNpos]
        nlinarith
      rw [habs] at hq'
      linarith
    · push_neg at hle
      exact hle
  have hqle : q ≤ 1 := by
    by_cases hle : q ≤ 1
    · exact hle
    · exfalso
      push_neg at hle
      have hlt' : ¬ (q.num ≤ (q.den:ℤ)) := by
        intro hc
        have h1 : q ≤ 1 := Rat.num_le_denom_iff.mp hc
        linarith
      have hnumg : (q.den:ℤ) < q.num := lt_of_not_ge hlt'
      have hz : (1:ℤ) ≤ q.num - (q.den:ℤ) := by omega
      have hzR : (1:ℝ) ≤ (q.num:ℝ) - (q.den:ℝ) := by exact_mod_cast hz
      have hsub : (q:ℝ) - 1 = ((q.num:ℝ) - (q.den:ℝ))/(q.den:ℝ) := by
        rw [hcast]
        field_simp
      have h1 : (1:ℝ)/(q.den:ℝ) ≤ (q:ℝ) - 1 := by
        rw [hsub, div_le_div_iff₀ hdenR hdenR]
        nlinarith
      have h2 : (q:ℝ) - 1 ≤ (q:ℝ) - m := by linarith
      have h3 : |m - (q:ℝ)| = (q:ℝ) - m := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith [hdeninv])
      have h4 : 1/(((N:ℝ)+1)*(q.den:ℝ)) < 1/(q.den:ℝ) := by
        rw [div_lt_div_iff₀ (by positivity) hdenR]
        nlinarith
      rw [h3] at hq'
      linarith
  have hnumpos : (0:ℤ) < q.num := Rat.num_pos.mpr hqpos
  have hnat : ((q.num.natAbs : ℕ) : ℝ) = (q.num:ℝ) := by
    have h : ((q.num.natAbs : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnumpos)
    have h2 := congrArg (fun z : ℤ => (z:ℝ)) h
    simpa using h2
  refine ⟨q.num.natAbs, q.den, ?_, ?_, hqN, q.reduced, ?_⟩
  · have hnn : (0:ℤ) ≤ q.num := le_of_lt hnumpos
    have habs : ((q.num.natAbs : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg hnn
    omega
  · have hnumle : q.num ≤ (q.den:ℤ) := Rat.num_le_denom_iff.mpr hqle
    have hnn : (0:ℤ) ≤ q.num := le_of_lt hnumpos
    have habs : ((q.num.natAbs : ℕ) : ℤ) = q.num := Int.natAbs_of_nonneg hnn
    omega
  · rw [hnat, ← hcast]
    exact hq'

/-- Distinct lowest-terms fractions differ by at least `1/(b*v)`. -/
private lemma frac_gap {a b u v : ℕ} (hb : 0 < b) (hv : 0 < v)
    (hne : (a:ℝ)/(b:ℝ) ≠ (u:ℝ)/(v:ℝ)) :
    (1:ℝ)/((b:ℝ)*(v:ℝ)) ≤ |(a:ℝ)/(b:ℝ) - (u:ℝ)/(v:ℝ)| := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv
  have hbv : (0:ℝ) < (b:ℝ)*(v:ℝ) := by positivity
  have hneZ : ((a:ℤ) * (v:ℤ) - (u:ℤ) * (b:ℤ)) ≠ 0 := by
    intro h
    apply hne
    have hR : (a:ℝ)*(v:ℝ) - (u:ℝ)*(b:ℝ) = 0 := by exact_mod_cast h
    rw [div_eq_div_iff (ne_of_gt hbR) (ne_of_gt hvR)]
    linarith
  have hone : (1:ℝ) ≤ |(((a:ℤ) * (v:ℤ) - (u:ℤ) * (b:ℤ) : ℤ) : ℝ)| := by
    have h := Int.one_le_abs hneZ
    exact_mod_cast h
  have heq : (a:ℝ)/(b:ℝ) - (u:ℝ)/(v:ℝ) =
      ((((a:ℤ) * (v:ℤ) - (u:ℤ) * (b:ℤ) : ℤ) : ℝ))/((b:ℝ)*(v:ℝ)) := by
    push_cast
    field_simp
    try ring
  have h1 : (1:ℝ)/((b:ℝ)*(v:ℝ)) ≤
      |(((a:ℤ) * (v:ℤ) - (u:ℤ) * (b:ℤ) : ℤ) : ℝ)|/((b:ℝ)*(v:ℝ)) := by
    rw [div_le_div_iff₀ hbv hbv]
    nlinarith
  simpa [heq, abs_div, abs_of_pos hbv] using h1

/-- Equal values of two lowest-terms fractions force equal denominators. -/
private lemma frac_den_eq {a b u v : ℕ} (hb : 0 < b) (hv : 0 < v)
    (h1 : Nat.Coprime a b) (h2 : Nat.Coprime u v)
    (h : (a:ℝ)/(b:ℝ) = (u:ℝ)/(v:ℝ)) : b = v := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv
  have hcross : (a:ℝ)*(v:ℝ) = (u:ℝ)*(b:ℝ) := by
    rw [div_eq_div_iff (ne_of_gt hbR) (ne_of_gt hvR)] at h
    linarith
  have hcrossN : a * v = u * b := by exact_mod_cast hcross
  have hdv : v ∣ b := by
    have hdiv : v ∣ u * b := ⟨a, by rw [← hcrossN]; ring⟩
    exact h2.symm |>.dvd_of_dvd_mul_left hdiv
  have hdb : b ∣ v := by
    have hdiv : b ∣ a * v := ⟨u, by rw [hcrossN, mul_comm]⟩
    exact h1.symm |>.dvd_of_dvd_mul_left hdiv
  exact Nat.dvd_antisymm hdb hdv

/-- A positive integer whose product with `N+1` is at most `2N` must be one. -/
private lemma det_eq_one {N k : ℕ} (hk : 0 < k)
    (h : (k:ℝ) * ((N:ℝ) + 1) ≤ 2 * (N:ℝ)) : k = 1 := by
  have hle1 : k ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hc
    nlinarith
  omega

/-- The core of the Farey gap bound: the Dirichlet approximant to the midpoint of two
consecutive reduced fractions is forced to be one of them, which bounds the gap. -/
private theorem det_one_of_consec (N : ℕ) {a₁ b₁ a₂ b₂ u v : ℕ}
    (hb₁ : 0 < b₁) (hcop₁ : Nat.Coprime a₁ b₁)
    (hb₂ : 0 < b₂) (hcop₂ : Nat.Coprime a₂ b₂)
    (hb₁N : b₁ ≤ N) (hb₂N : b₂ ≤ N) (hvN : v ≤ N)
    (huv : u ≤ v) (hcopuv : Nat.Coprime u v) (hu1 : 1 ≤ u)
    (hlt : (a₁:ℝ)/(b₁:ℝ) < (a₂:ℝ)/(b₂:ℝ))
    (hnob : ∀ r : ℕ × ℕ, 1 ≤ r.1 → r.1 ≤ N → 1 ≤ r.2 → r.2 ≤ N → r.1 ≤ r.2 →
      Nat.Coprime r.1 r.2 → (a₁:ℝ)/(b₁:ℝ) < (r.1:ℝ)/(r.2:ℝ) →
      (r.1:ℝ)/(r.2:ℝ) < (a₂:ℝ)/(b₂:ℝ) → False)
    (happ : |((a₁:ℝ)/(b₁:ℝ) + (a₂:ℝ)/(b₂:ℝ))/2 - (u:ℝ)/(v:ℝ)| ≤
      1/(((N:ℝ)+1)*(v:ℝ))) :
    a₂ * b₁ - a₁ * b₂ = 1 := by
  have hb₁R : (0:ℝ) < (b₁:ℝ) := by exact_mod_cast hb₁
  have hb₂R : (0:ℝ) < (b₂:ℝ) := by exact_mod_cast hb₂
  have hv0 : 0 < v := by omega
  have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv0
  have hcrossN : a₁ * b₂ < a₂ * b₁ := by
    have h := (div_lt_div_iff₀ hb₁R hb₂R).mp hlt
    exact_mod_cast h
  set k : ℕ := a₂ * b₁ - a₁ * b₂ with hk
  have hkpos : 0 < k := by rw [hk]; exact Nat.sub_pos_of_lt hcrossN
  have hkR : (k:ℝ) = (a₂:ℝ)*(b₁:ℝ) - (a₁:ℝ)*(b₂:ℝ) := by
    rw [hk, Nat.cast_sub (le_of_lt hcrossN)]
    push_cast
    ring
  have hgk : (a₂:ℝ)/(b₂:ℝ) - (a₁:ℝ)/(b₁:ℝ) = (k:ℝ)/((b₁:ℝ)*(b₂:ℝ)) := by
    rw [hkR]
    field_simp
    try ring
  have hnotbetween : ¬ ((a₁:ℝ)/(b₁:ℝ) < (u:ℝ)/(v:ℝ) ∧ (u:ℝ)/(v:ℝ) < (a₂:ℝ)/(b₂:ℝ)) := by
    rintro ⟨h1, h2⟩
    exact hnob (u, v) hu1 (le_trans huv hvN) (by omega) hvN huv hcopuv h1 h2
  have hfin : (k:ℝ) * ((N:ℝ)+1) ≤ 2*(N:ℝ) := by
    have hpm : ((a₁:ℝ)/(b₁:ℝ) + (a₂:ℝ)/(b₂:ℝ))/2 - (u:ℝ)/(v:ℝ) ≤
        1/(((N:ℝ)+1)*(v:ℝ)) := (abs_le.mp happ).2
    have hmp : -((1:ℝ)/(((N:ℝ)+1)*(v:ℝ))) ≤
        ((a₁:ℝ)/(b₁:ℝ) + (a₂:ℝ)/(b₂:ℝ))/2 - (u:ℝ)/(v:ℝ) := (abs_le.mp happ).1
    by_cases hle : (u:ℝ)/(v:ℝ) ≤ (a₁:ℝ)/(b₁:ℝ)
    · have hbound : (k:ℝ)/((b₁:ℝ)*(b₂:ℝ))/2 ≤ 1/(((N:ℝ)+1)*(v:ℝ)) := by
        rw [← hgk]
        linarith
      have hveq : v = b₁ := by
        by_cases heq : (u:ℝ)/(v:ℝ) = (a₁:ℝ)/(b₁:ℝ)
        · exact frac_den_eq hv0 hb₁ hcopuv hcop₁ heq
        · exfalso
          have hlt' : (u:ℝ)/(v:ℝ) < (a₁:ℝ)/(b₁:ℝ) := lt_of_le_of_ne hle heq
          have hgap : (1:ℝ)/((b₁:ℝ)*(v:ℝ)) ≤ (a₁:ℝ)/(b₁:ℝ) - (u:ℝ)/(v:ℝ) := by
            have h := frac_gap hb₁ hv0 (Ne.symm (ne_of_lt hlt'))
            rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ (a₁:ℝ)/(b₁:ℝ) - (u:ℝ)/(v:ℝ))] at h
          have hlt1 : (1:ℝ)/(((N:ℝ)+1)*(v:ℝ)) < (1:ℝ)/((b₁:ℝ)*(v:ℝ)) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]
            have hb1N' : (b₁:ℝ) ≤ (N:ℝ) := by exact_mod_cast hb₁N
            nlinarith
          have h2 : (a₁:ℝ)/(b₁:ℝ) - (u:ℝ)/(v:ℝ) ≤
              1/(((N:ℝ)+1)*(v:ℝ)) - ((a₂:ℝ)/(b₂:ℝ) - (a₁:ℝ)/(b₁:ℝ))/2 := by linarith
          linarith
      rw [hveq] at hbound
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at hbound
      have hkey : (k:ℝ)/((b₁:ℝ)*(b₂:ℝ)) * (((N:ℝ)+1)*(b₁:ℝ)) =
          (k:ℝ)*((N:ℝ)+1)/(b₂:ℝ) := by
        field_simp
        try ring
      rw [hkey] at hbound
      rw [div_le_iff₀ hb₂R] at hbound
      have hb2N' : (b₂:ℝ) ≤ (N:ℝ) := by exact_mod_cast hb₂N
      linarith
    · push_neg at hle
      have hge : (a₂:ℝ)/(b₂:ℝ) ≤ (u:ℝ)/(v:ℝ) := by
        by_contra hc
        push_neg at hc
        exact hnotbetween ⟨hle, hc⟩
      have hbound : (k:ℝ)/((b₁:ℝ)*(b₂:ℝ))/2 ≤ 1/(((N:ℝ)+1)*(v:ℝ)) := by
        rw [← hgk]
        linarith
      have hveq : v = b₂ := by
        by_cases heq : (u:ℝ)/(v:ℝ) = (a₂:ℝ)/(b₂:ℝ)
        · exact frac_den_eq hv0 hb₂ hcopuv hcop₂ heq
        · exfalso
          have hlt' : (a₂:ℝ)/(b₂:ℝ) < (u:ℝ)/(v:ℝ) := lt_of_le_of_ne hge (Ne.symm heq)
          have hgap : (1:ℝ)/((b₂:ℝ)*(v:ℝ)) ≤ (u:ℝ)/(v:ℝ) - (a₂:ℝ)/(b₂:ℝ) := by
            have h := frac_gap hb₂ hv0 (ne_of_lt hlt')
            rw [abs_of_nonpos (by linarith : (a₂:ℝ)/(b₂:ℝ) - (u:ℝ)/(v:ℝ) ≤ 0)] at h
            linarith
          have hlt1 : (1:ℝ)/(((N:ℝ)+1)*(v:ℝ)) < (1:ℝ)/((b₂:ℝ)*(v:ℝ)) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]
            have hb2N' : (b₂:ℝ) ≤ (N:ℝ) := by exact_mod_cast hb₂N
            nlinarith
          have h2 : (u:ℝ)/(v:ℝ) - (a₂:ℝ)/(b₂:ℝ) ≤
              1/(((N:ℝ)+1)*(v:ℝ)) - ((a₂:ℝ)/(b₂:ℝ) - (a₁:ℝ)/(b₁:ℝ))/2 := by linarith
          linarith
      rw [hveq] at hbound
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at hbound
      have hkey : (k:ℝ)/((b₁:ℝ)*(b₂:ℝ)) * (((N:ℝ)+1)*(b₂:ℝ)) =
          (k:ℝ)*((N:ℝ)+1)/(b₁:ℝ) := by
        field_simp
        try ring
      rw [hkey] at hbound
      rw [div_le_iff₀ hb₁R] at hbound
      have hb1N' : (b₁:ℝ) ≤ (N:ℝ) := by exact_mod_cast hb₁N
      linarith
  exact det_eq_one hkpos hfin

/-- Consecutive reduced fractions with denominator `≤ N` have denominators summing to
more than `N`, because otherwise the mediant would lie between them. -/
private lemma mediant_gap {N : ℕ} {a₁ b₁ a₂ b₂ : ℕ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    (hn₁ : 1 ≤ a₁) (hn₂ : 1 ≤ a₂)
    (hlt : (a₁:ℝ)/(b₁:ℝ) < (a₂:ℝ)/(b₂:ℝ))
    (hnob : ∀ r : ℕ × ℕ, 1 ≤ r.1 → r.1 ≤ N → 1 ≤ r.2 → r.2 ≤ N → r.1 ≤ r.2 → Nat.Coprime r.1 r.2 →
      (a₁:ℝ)/(b₁:ℝ) < (r.1:ℝ)/(r.2:ℝ) → (r.1:ℝ)/(r.2:ℝ) < (a₂:ℝ)/(b₂:ℝ) → False) :
    N < b₁ + b₂ := by
  by_contra hcon
  push_neg at hcon
  have hb₁R : (0:ℝ) < (b₁:ℝ) := by exact_mod_cast hb₁
  have hb₂R : (0:ℝ) < (b₂:ℝ) := by exact_mod_cast hb₂
  have hcross : (a₁:ℝ)*(b₂:ℝ) < (a₂:ℝ)*(b₁:ℝ) := by
    have h := (div_lt_div_iff₀ hb₁R hb₂R).mp hlt
    simpa using h
  set g : ℕ := Nat.gcd (a₁ + a₂) (b₁ + b₂) with hg
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) (by omega)
  have hgR : (0:ℝ) < (g:ℝ) := by exact_mod_cast hgpos
  have hgdl : g ∣ a₁ + a₂ := Nat.gcd_dvd_left _ _
  have hgdr : g ∣ b₁ + b₂ := Nat.gcd_dvd_right _ _
  have hc1 : (((a₁ + a₂)/g : ℕ) : ℝ) = ((a₁:ℝ) + (a₂:ℝ))/(g:ℝ) := by
    rw [Nat.cast_div hgdl (by exact_mod_cast hgpos.ne')]
    push_cast
    ring
  have hc2 : (((b₁ + b₂)/g : ℕ) : ℝ) = ((b₁:ℝ) + (b₂:ℝ))/(g:ℝ) := by
    rw [Nat.cast_div hgdr (by exact_mod_cast hgpos.ne')]
    push_cast
    ring
  have hmedval : (((a₁ + a₂)/g : ℕ) : ℝ)/(((b₁ + b₂)/g : ℕ):ℝ) =
      ((a₁:ℝ) + (a₂:ℝ))/((b₁:ℝ) + (b₂:ℝ)) := by
    rw [hc1, hc2]
    field_simp
  have hab : a₁ + a₂ ≤ b₁ + b₂ := by omega
  have hmem : 1 ≤ (a₁ + a₂)/g ∧ (a₁ + a₂)/g ≤ N ∧ 1 ≤ (b₁ + b₂)/g ∧ (b₁ + b₂)/g ≤ N ∧
      (a₁ + a₂)/g ≤ (b₁ + b₂)/g ∧ Nat.Coprime ((a₁ + a₂)/g) ((b₁ + b₂)/g) := by
    have h1' : (0:ℕ) < (a₁ + a₂)/g := Nat.div_pos (Nat.le_of_dvd (by omega) hgdl) hgpos
    have h2 : (a₁ + a₂)/g ≤ N := le_trans (Nat.div_le_self _ _) (le_trans hab hcon)
    have h3' : (0:ℕ) < (b₁ + b₂)/g := Nat.div_pos (Nat.le_of_dvd (by omega) hgdr) hgpos
    have h4 : (b₁ + b₂)/g ≤ N := le_trans (Nat.div_le_self _ _) hcon
    have h5 : (a₁ + a₂)/g ≤ (b₁ + b₂)/g := Nat.div_le_div_right hab
    exact ⟨h1', h2, h3', h4, h5, Nat.coprime_div_gcd_div_gcd (by omega)⟩
  have h1 : (a₁:ℝ)/(b₁:ℝ) < (((a₁ + a₂)/g : ℕ) : ℝ)/(((b₁ + b₂)/g : ℕ):ℝ) := by
    rw [hmedval, div_lt_div_iff₀ hb₁R (by linarith)]
    nlinarith
  have h2 : (((a₁ + a₂)/g : ℕ) : ℝ)/(((b₁ + b₂)/g : ℕ):ℝ) < (a₂:ℝ)/(b₂:ℝ) := by
    rw [hmedval, div_lt_div_iff₀ (by linarith) hb₂R]
    nlinarith
  exact hnob ((a₁ + a₂)/g, (b₁ + b₂)/g) hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2.1
    hmem.2.2.2.2.1 hmem.2.2.2.2.2 h1 h2

/-- The Farey gap bound: the boxes of radius `1/(q*Q)` about the nearest reduced
fractions below and above `m` overlap. -/
private theorem farey_gap (Q : ℝ) (N : ℕ) (hN2 : 2 ≤ N) (hNQ : (N:ℝ) ≤ Q)
    (hQN : Q < (N:ℝ) + 1) {m : ℝ} (hmN : 1/(N:ℝ) ≤ m) (hm1 : m ≤ 1) :
    ∃ a b c d : ℕ, (1 ≤ b ∧ b ≤ N ∧ 1 ≤ a ∧ a ≤ b ∧ Nat.Coprime a b) ∧
      (1 ≤ d ∧ d ≤ N ∧ 1 ≤ c ∧ c ≤ d ∧ Nat.Coprime c d) ∧
      (a:ℝ)/(b:ℝ) ≤ m ∧ m ≤ (c:ℝ)/(d:ℝ) ∧
      ((c:ℝ)/(d:ℝ) - (a:ℝ)/(b:ℝ)) ≤ 1/((b:ℝ)*Q) + 1/((d:ℝ)*Q) := by
  classical
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hN2
  have hNpos : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr hN0
  have hQpos : (0:ℝ) < Q := by
    have h2Q : (2:ℝ) ≤ Q := le_trans (by exact_mod_cast hN2) hNQ
    linarith
  have hmN' : (0:ℝ) < 1/(N:ℝ) := one_div_pos.mpr hNpos
  set A : Finset (ℕ × ℕ) := (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2)) with hA
  have hmem : ∀ p : ℕ × ℕ, p ∈ A ↔
      (1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2) := by
    intro p
    rw [hA, mem_farey_pair]
  have h1N : (1, N) ∈ A := by
    rw [hmem]; exact ⟨le_refl 1, by omega, by omega, le_refl N, by omega, Nat.coprime_one_left N⟩
  have h11 : (1, 1) ∈ A := by
    rw [hmem]; exact ⟨le_rfl, by omega, le_rfl, by omega, le_rfl, Nat.coprime_one_left 1⟩
  have hlow : ∀ p : ℕ × ℕ, p ∈ A → (1:ℝ)/(N:ℝ) ≤ (p.1:ℝ)/(p.2:ℝ) := by
    intro p hp
    rw [hmem] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    have h1' : (1:ℝ) ≤ (p.1:ℝ) := by exact_mod_cast h1
    have h3' : (0:ℝ) < (p.2:ℝ) := by exact_mod_cast h3
    have h4' : (p.2:ℝ) ≤ (N:ℝ) := by exact_mod_cast h4
    rw [div_le_div_iff₀ hNpos h3']
    nlinarith
  have hhigh : ∀ p : ℕ × ℕ, p ∈ A → (p.1:ℝ)/(p.2:ℝ) ≤ 1 := by
    intro p hp
    rw [hmem] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    have h3' : (0:ℝ) < (p.2:ℝ) := by exact_mod_cast h3
    have h5' : (p.1:ℝ) ≤ (p.2:ℝ) := by exact_mod_cast h5
    rw [div_le_one h3']
    exact h5'
  obtain ⟨p₁, hp₁, hmax⟩ := Finset.exists_max_image
      (A.filter (fun p : ℕ × ℕ => (p.1:ℝ)/(p.2:ℝ) ≤ m)) (fun p : ℕ × ℕ => (p.1:ℝ)/(p.2:ℝ))
      ⟨(1, N), by
        rw [Finset.mem_filter]
        exact ⟨h1N, by simpa using hmN⟩⟩
  obtain ⟨p₂, hp₂, hmin⟩ := Finset.exists_min_image
      (A.filter (fun p : ℕ × ℕ => m ≤ (p.1:ℝ)/(p.2:ℝ))) (fun p : ℕ × ℕ => (p.1:ℝ)/(p.2:ℝ))
      ⟨(1, 1), by
        rw [Finset.mem_filter]
        exact ⟨h11, by simpa using hm1⟩⟩
  rw [Finset.mem_filter] at hp₁ hp₂
  obtain ⟨hp₁A, hp₁v⟩ := hp₁
  obtain ⟨hp₂A, hp₂v⟩ := hp₂
  have hp₁B := (hmem p₁).mp hp₁A
  have hp₂B := (hmem p₂).mp hp₂A
  obtain ⟨ha1, haN, hb1, hbN, hab, hcab⟩ := hp₁B
  obtain ⟨hc1, hcN, hd1, hdN, hcd, hccd⟩ := hp₂B
  have hbpos : (0:ℝ) < (p₁.2:ℝ) := by exact_mod_cast hb1
  have hdpos : (0:ℝ) < (p₂.2:ℝ) := by exact_mod_cast hd1
  have hnob' : ∀ r : ℕ × ℕ, 1 ≤ r.1 → r.1 ≤ N → 1 ≤ r.2 → r.2 ≤ N → r.1 ≤ r.2 →
      Nat.Coprime r.1 r.2 → (p₁.1:ℝ)/(p₁.2:ℝ) < (r.1:ℝ)/(r.2:ℝ) →
      (r.1:ℝ)/(r.2:ℝ) < (p₂.1:ℝ)/(p₂.2:ℝ) → False := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8
    have hrA : r ∈ A := (hmem r).mpr ⟨h1, h2, h3, h4, h5, h6⟩
    by_cases hle : (r.1:ℝ)/(r.2:ℝ) ≤ m
    · have := hmax r (by rw [Finset.mem_filter]; exact ⟨hrA, hle⟩)
      linarith
    · push_neg at hle
      have := hmin r (by rw [Finset.mem_filter]; exact ⟨hrA, le_of_lt hle⟩)
      linarith
  refine ⟨p₁.1, p₁.2, p₂.1, p₂.2, ⟨hb1, hbN, ha1, hab, hcab⟩, ⟨hd1, hdN, hc1, hcd, hccd⟩,
    hp₁v, hp₂v, ?_⟩
  by_cases hsmall : (p₂.1:ℝ)/(p₂.2:ℝ) ≤ (p₁.1:ℝ)/(p₁.2:ℝ)
  · have h1 : (0:ℝ) ≤ 1/((p₁.2:ℝ)*Q) := by positivity
    have h2 : (0:ℝ) ≤ 1/((p₂.2:ℝ)*Q) := by positivity
    linarith
  · push_neg at hsmall
    have hcross : (p₁.1:ℝ)*(p₂.2:ℝ) < (p₂.1:ℝ)*(p₁.2:ℝ) := by
      have h := (div_lt_div_iff₀ hbpos hdpos).mp hsmall
      simpa using h
    have hbdN : N < p₁.2 + p₂.2 := mediant_gap hb1 hd1 hab hcd ha1 hc1 hsmall hnob'
    set mstar : ℝ := ((p₁.1:ℝ)/(p₁.2:ℝ) + (p₂.1:ℝ)/(p₂.2:ℝ))/2 with hmstar
    have hmstarN : 1/(N:ℝ) ≤ mstar := by
      have h := hlow p₁ hp₁A
      rw [hmstar]; linarith
    have hmstar1 : mstar ≤ 1 := by
      have h := hhigh p₂ hp₂A
      rw [hmstar]; linarith
    obtain ⟨u, v, hu1, huv, hvN, hcuv, happ⟩ := dyadic_approx N hN0 hmstarN hmstar1
    have hk1 : p₂.1 * p₁.2 - p₁.1 * p₂.2 = 1 := by
      refine det_one_of_consec N hb1 hcab hd1 hccd hbN hdN hvN huv hcuv hu1 hsmall hnob' ?_
      simpa [hmstar] using happ
    have hcrossN : p₁.1 * p₂.2 < p₂.1 * p₁.2 := by exact_mod_cast hcross
    have hnumR : ((p₂.1 * p₁.2 - p₁.1 * p₂.2 : ℕ) : ℝ) = 1 := by
      rw [hk1]; norm_num
    have hcrossR : (1:ℝ) = (p₂.1:ℝ)*(p₁.2:ℝ) - (p₁.1:ℝ)*(p₂.2:ℝ) := by
      rw [← hnumR, Nat.cast_sub (le_of_lt hcrossN)]
      push_cast
      ring
    have hgapval : (p₂.1:ℝ)/(p₂.2:ℝ) - (p₁.1:ℝ)/(p₁.2:ℝ) = 1/((p₁.2:ℝ)*(p₂.2:ℝ)) := by
      have e1 : (p₂.1:ℝ)/(p₂.2:ℝ) - (p₁.1:ℝ)/(p₁.2:ℝ) =
          ((p₂.1:ℝ)*(p₁.2:ℝ) - (p₁.1:ℝ)*(p₂.2:ℝ))/((p₁.2:ℝ)*(p₂.2:ℝ)) := by
        field_simp
        try ring
      rw [e1, ← hcrossR]
    have hQbd : Q ≤ (p₁.2:ℝ) + (p₂.2:ℝ) := by
      have h1 : N + 1 ≤ p₁.2 + p₂.2 := by omega
      have h2 : ((N:ℝ) + 1) ≤ (p₁.2:ℝ) + (p₂.2:ℝ) := by exact_mod_cast h1
      linarith
    rw [hgapval]
    have hsplit : (1:ℝ)/((p₁.2:ℝ)*Q) + 1/((p₂.2:ℝ)*Q) =
        ((p₂.2:ℝ) + (p₁.2:ℝ))/((p₁.2:ℝ)*(p₂.2:ℝ)*Q) := by
      field_simp
      try ring
    rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
    have hbdpos : (0:ℝ) < (p₁.2:ℝ)*(p₂.2:ℝ) := by positivity
    nlinarith [hbdpos, hQbd]

/-- A point fails to lie in the open symmetric interval exactly when its modulus is
at least the radius. -/
private lemma not_mem_Ioo_abs (c t : ℝ) : t ∉ Set.Ioo (-c) c ↔ c ≤ |t| := by
  have hmem : t ∈ Set.Ioo (-c) c ↔ |t| < c := by
    rw [Set.mem_Ioo, abs_lt]
  rw [hmem, not_lt]

/-- Membership in the punctured rational envelope. -/
private lemma mem_puncturedEnvelope {N Y H B : ℝ} {q : ℕ} {t : ℝ} :
    t ∈ puncturedEnvelope N Y H B q ↔
      (|t| ≤ 1/((q:ℝ)*fareyOrder H) ∧
        ((q:ℝ) ≤ Real.log N ^ B →
          Real.log N ^ (2*B)/((q:ℝ)*Y) ≤ |t|)) := by
  unfold puncturedEnvelope
  have h1 : t ∈ Set.Icc (-(1/((q:ℝ)*fareyOrder H))) (1/((q:ℝ)*fareyOrder H)) ↔
      |t| ≤ 1/((q:ℝ)*fareyOrder H) := by
    rw [Set.mem_Icc, abs_le]
  by_cases h : (q:ℝ) ≤ Real.log N ^ B
  · rw [if_pos h, Set.mem_sdiff, h1, not_mem_Ioo_abs]
    simp [h]
  · rw [if_neg h, Set.sdiff_empty, h1]
    simp [h]

/-- Two boxes of the Farey kind cover a segment of length at most `1/(2Q^2)` inside one
period `[1/Q, 1 + 1/Q]`. -/
private theorem box_pair (Q : ℝ) (N : ℕ) (hN2 : 2 ≤ N) (hNQ : (N:ℝ) ≤ Q)
    (hQN : Q < (N:ℝ) + 1) (L U : ℝ) (hLQ : 1/Q ≤ L) (hUQ : U ≤ 1 + 1/Q)
    (hLU : U - L ≤ 1/(2*Q^2)) :
    ∃ a₁ b₁ a₂ b₂ : ℕ,
      (1 ≤ b₁ ∧ (b₁:ℝ) ≤ Q ∧ 1 ≤ a₁ ∧ a₁ ≤ b₁ ∧ Nat.Coprime a₁ b₁) ∧
      (1 ≤ b₂ ∧ (b₂:ℝ) ≤ Q ∧ 1 ≤ a₂ ∧ a₂ ≤ b₂ ∧ Nat.Coprime a₂ b₂) ∧
      Set.Icc L U ⊆
        Set.Icc ((a₁:ℝ)/b₁ - 1/((b₁:ℝ)*Q)) ((a₁:ℝ)/b₁ + 1/((b₁:ℝ)*Q)) ∪
        Set.Icc ((a₂:ℝ)/b₂ - 1/((b₂:ℝ)*Q)) ((a₂:ℝ)/b₂ + 1/((b₂:ℝ)*Q)) := by
  have hQpos : (0:ℝ) < Q := by
    have h2Q : (2:ℝ) ≤ Q := le_trans (by exact_mod_cast hN2) hNQ
    linarith
  have hN0 : (0:ℕ) < N := lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hN2
  have hNpos : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr hN0
  have h1Q : ((1:ℕ) : ℝ) ≤ Q :=
    le_trans (by exact_mod_cast (show (1:ℕ) ≤ N from le_trans (by norm_num) hN2)) hNQ
  rcases lt_or_ge U L with hUL | hUL
  · refine ⟨1, 1, 1, 1, ⟨le_rfl, h1Q, le_rfl, le_rfl, Nat.coprime_one_left 1⟩,
      ⟨le_rfl, h1Q, le_rfl, le_rfl, Nat.coprime_one_left 1⟩, ?_⟩
    rintro α ⟨h1, h2⟩
    exfalso
    linarith
  · by_cases hc1 : (L + U)/2 < 1/(N:ℝ)
    · -- a single box about `1/N` covers the segment
      refine ⟨1, N, 1, N, ⟨by omega, hNQ, le_rfl, by omega, Nat.coprime_one_left N⟩,
        ⟨by omega, hNQ, le_rfl, by omega, Nat.coprime_one_left N⟩, ?_⟩
      rintro α ⟨hαL, hαU⟩
      have hq : Q - (N:ℝ) < 1 := by linarith
      have hNQpos : (0:ℝ) < (N:ℝ)*Q := by positivity
      have hA : (1:ℝ)/(N:ℝ) - 1/((N:ℝ)*Q) ≤ 1/Q := by
        have e : (1:ℝ)/(N:ℝ) - 1/((N:ℝ)*Q) = (Q - 1)/((N:ℝ)*Q) := by
          field_simp
          try ring
        rw [e, div_le_div_iff₀ hNQpos hQpos]
        nlinarith [hQN, hQpos, hNpos]
      have hB : (1:ℝ)/(N:ℝ) - 1/Q ≤ 1/((N:ℝ)*Q) := by
        have e : (1:ℝ)/(N:ℝ) - 1/Q = (Q - (N:ℝ))/((N:ℝ)*Q) := by
          field_simp
          try ring
        rw [e, div_le_div_iff₀ hNQpos hNQpos]
        nlinarith [hq]
      have h2N : (2:ℝ)/(N:ℝ) = 2 * (1/(N:ℝ)) := by ring
      have h4 : (2:ℝ)/(N:ℝ) - 1/Q ≤ (1:ℝ)/(N:ℝ) + 1/((N:ℝ)*Q) := by
        rw [h2N]
        linarith
      refine Or.inl ⟨?_, ?_⟩
      · linarith [hA, hαL, hLQ]
      · have h2 : U < 2/(N:ℝ) - L := by
          rw [h2N]
          linarith
        rw [h2N] at h4
        linarith [h4, hLQ]
    · by_cases hc2 : 1 < (L + U)/2
      · -- a single box about `1` covers the segment
        refine ⟨1, 1, 1, 1, ⟨le_rfl, h1Q, le_rfl, le_rfl, Nat.coprime_one_left 1⟩,
          ⟨le_rfl, h1Q, le_rfl, le_rfl, Nat.coprime_one_left 1⟩, ?_⟩
        rintro α ⟨hαL, hαU⟩
        have hαlo : (1:ℝ) - 1/Q ≤ α := by linarith
        have hαhi : α ≤ 1 + 1/Q := le_trans hαU hUQ
        have e1 : (1:ℝ)/1 - 1/((1:ℝ)*Q) = 1 - 1/Q := by
          field_simp
        have e2 : (1:ℝ)/1 + 1/((1:ℝ)*Q) = 1 + 1/Q := by
          field_simp
        have hgoal : α ∈ Set.Icc ((1:ℝ)/1 - 1/((1:ℝ)*Q)) ((1:ℝ)/1 + 1/((1:ℝ)*Q)) := by
          rw [Set.mem_Icc, e1, e2]
          exact ⟨hαlo, hαhi⟩
        exact Or.inl (by simpa using hgoal)
      · -- the Farey pair at the midpoint
        push_neg at hc1 hc2
        obtain ⟨a₁, b₁, a₂, b₂, hc₁, hc₂, hv1, hv2, hgap⟩ :=
          farey_gap Q N hN2 hNQ hQN hc1 hc2
        have hb1pos : (0:ℝ) < (b₁:ℝ) := by exact_mod_cast hc₁.1
        have hb2pos : (0:ℝ) < (b₂:ℝ) := by exact_mod_cast hc₂.1
        have hb1Q : (b₁:ℝ) ≤ Q := le_trans (by exact_mod_cast hc₁.2.1) hNQ
        have hb2Q : (b₂:ℝ) ≤ Q := le_trans (by exact_mod_cast hc₂.2.1) hNQ
        refine ⟨a₁, b₁, a₂, b₂, ⟨hc₁.1, hb1Q, hc₁.2.2.1, hc₁.2.2.2.1, hc₁.2.2.2.2⟩,
          ⟨hc₂.1, hb2Q, hc₂.2.2.1, hc₂.2.2.2.1, hc₂.2.2.2.2⟩, ?_⟩
        refine segment_two_box ?_ ?_ ?_
        · have hmL : (L + U)/2 - L ≤ 1/(2*Q^2) := by linarith
          have hr1 : (1:ℝ)/(2*Q^2) ≤ 1/((b₁:ℝ)*Q) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hQpos, hb1pos, hb1Q]
          linarith
        · have hUm : U - (L + U)/2 ≤ 1/(2*Q^2) := by linarith
          have hr2 : (1:ℝ)/(2*Q^2) ≤ 1/((b₂:ℝ)*Q) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hQpos, hb2pos, hb2Q]
          linarith
        · exact hgap


/-- Page 46 display 14: integration over two covering pieces costs at most
 twice a uniform mass bound. No disjointness hypothesis is needed. -/
theorem two_piece_mass_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} {D A B : Set α} {V : ℝ}
    (hA : MeasurableSet A) (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ)
    (hf0 : ∀ x, 0 ≤ f x) (hcover : D ⊆ A ∪ B)
    (hVA : (∫ x in A, f x ∂μ) ≤ V) (hVB : (∫ x in B, f x ∂μ) ≤ V) :
    (∫ x in D, f x ∂μ) ≤ 2 * V := by
  have hfD := (hfA.union hfB).mono_set hcover
  have hDA : D ∩ A ⊆ A := Set.inter_subset_right
  have hDB : D \ A ⊆ B := by
    intro x hx
    exact (hcover hx.1).resolve_left hx.2
  have hleft := setIntegral_mono_set hfA (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hDA)
  have hright := setIntegral_mono_set hfB (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hDB)
  rw [← integral_inter_add_sdiff hA hfD]
  linarith

/-- Page 47 display 15: integrate the principal plus remainder square bound.
The integral is on the symmetric punctured envelope of the source Farey arc. -/
theorem arc_mass_from_parts (N Y H B : ℝ) (q a : ℕ) :
    (∫ t in puncturedEnvelope N Y H B q, ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2) ≤
      2 * (principalArcMass N Y H B q + remainderArcMass N Y H B q a) := by
  have hsub : puncturedEnvelope N Y H B q ⊆
      Set.Icc (-(1 / ((q : ℝ) * fareyOrder H))) (1 / ((q : ℝ) * fareyOrder H)) := Set.sdiff_subset
  have hS : IntegrableOn (fun t : ℝ => ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondSum phase
    fun_prop
  have hP : IntegrableOn (fun t : ℝ => ‖rationalWeight q * secondModel Y t‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondModel phase
    fun_prop
  have hR : IntegrableOn (fun t : ℝ => ‖secondRemainder Y q a t‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondRemainder secondSum secondModel phase
    fun_prop
  have hpoint (t : ℝ) : ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2 ≤
      2 * (‖rationalWeight q * secondModel Y t‖ ^ 2 + ‖secondRemainder Y q a t‖ ^ 2) := by
    convert Decomp279b.norm_add_sq (rationalWeight q * secondModel Y t) (secondRemainder Y q a t) using 1
    congr 2
    unfold secondRemainder
    ring
  calc (∫ t in puncturedEnvelope N Y H B q, ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2) ≤
      ∫ t in puncturedEnvelope N Y H B q,
        2 * (‖rationalWeight q * secondModel Y t‖ ^ 2 + ‖secondRemainder Y q a t‖ ^ 2) :=
      integral_mono hS ((hP.add hR).const_mul 2) hpoint
    _ = _ := by rw [integral_const_mul, integral_add hP hR]; rfl

/-- LEAF. Page 46 before display 14: the local minor set has a cover by
at most two punctured rational envelopes. This is the finite Farey geometry
only, with no integral, character, zero count or prime estimate. -/
theorem farey_two_envelope_cover :
    ∃ N₀ : ℝ, ∀ N Y H B : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
    ∀ ξ : ℝ, ∃ q₁ a₁ q₂ a₂ : ℕ,
      (1 ≤ q₁ ∧ (q₁ : ℝ) ≤ fareyOrder H ∧ 1 ≤ a₁ ∧ a₁ ≤ q₁ ∧ Nat.Coprime a₁ q₁) ∧
      (1 ≤ q₂ ∧ (q₂ : ℝ) ≤ fareyOrder H ∧ 1 ≤ a₂ ∧ a₂ ≤ q₂ ∧ Nat.Coprime a₂ q₂) ∧
      minorDomain N Y H B ∩ Set.Ioo (ξ - 1 / H) (ξ + 1 / H) ⊆
        {α : ℝ | α - (a₁ : ℝ) / q₁ ∈ puncturedEnvelope N Y H B q₁} ∪
        {α : ℝ | α - (a₂ : ℝ) / q₂ ∈ puncturedEnvelope N Y H B q₂} := by
  refine ⟨0, ?_⟩
  intro N Y H B _ hY hH hB ξ
  have hH0 : (0:ℝ) < H := by linarith
  have hsqrt4 : (4:ℝ) ≤ Real.sqrt H := by
    have h := Real.sqrt_le_sqrt hH
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hQ2 : 2 ≤ fareyOrder H := by
    rw [fareyOrder, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  set Q : ℝ := fareyOrder H with hQ
  have hQpos : (0:ℝ) < Q := by linarith
  have hQeq : Q = Real.sqrt H / 2 := by rw [hQ]; rfl
  have hsqH : (0:ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH0
  have hQsq : Q^2 = H/4 := by
    rw [hQeq, div_pow, Real.sq_sqrt (le_of_lt hH0)]
    norm_num
  have hone : (1:ℝ)/Q = 2/Real.sqrt H := by
    rw [hQeq]
    have hne : Real.sqrt H ≠ 0 := ne_of_gt hsqH
    field_simp
  set K : ℕ := ⌊Q⌋₊ with hK
  have hKle : (K:ℝ) ≤ Q := Nat.floor_le (le_of_lt hQpos)
  have hKlt : Q < (K:ℝ) + 1 := Nat.lt_floor_add_one Q
  have hK2 : 2 ≤ K := by
    have h : ((2:ℕ) : ℝ) ≤ Q := by push_cast; exact hQ2
    exact Nat.le_floor h
  set L : ℝ := max (2/Real.sqrt H) (ξ - 1/H) with hL
  set U : ℝ := min (1 + 2/Real.sqrt H) (ξ + 1/H) with hU
  have hLQ : (1:ℝ)/Q ≤ L := by
    rw [hL, hone]
    exact le_max_left _ _
  have hUQ : U ≤ 1 + 1/Q := by
    rw [hU, hone]
    exact min_le_left _ _
  have hLU : U - L ≤ 1/(2*Q^2) := by
    have h1 : ξ - 1/H ≤ L := le_max_right _ _
    have h2 : U ≤ ξ + 1/H := min_le_right _ _
    have h3 : (1:ℝ)/(2*Q^2) = 2*(1/H) := by
      rw [hQsq]
      have hHne : H ≠ 0 := ne_of_gt hH0
      field_simp
      try ring
    rw [h3]
    linarith
  obtain ⟨a₁, b₁, a₂, b₂, hc₁, hc₂, hcov⟩ := box_pair Q K hK2 hKle hKlt L U hLQ hUQ hLU
  refine ⟨b₁, a₁, b₂, a₂, ⟨hc₁.1, hc₁.2.1, hc₁.2.2.1, hc₁.2.2.2.1, hc₁.2.2.2.2⟩,
    ⟨hc₂.1, hc₂.2.1, hc₂.2.2.1, hc₂.2.2.2.1, hc₂.2.2.2.2⟩, ?_⟩
  intro α hα
  obtain ⟨hαper, hαmaj⟩ := hα.1
  have hαw := hα.2
  have hαL : L ≤ α := by
    rw [hL]
    exact max_le hαper.1 (le_of_lt hαw.1)
  have hαU : α ≤ U := by
    rw [hU]
    exact le_min hαper.2 (le_of_lt hαw.2)
  rcases hcov ⟨hαL, hαU⟩ with hbox | hbox
  · left
    change α - (a₁:ℝ)/b₁ ∈ puncturedEnvelope N Y H B b₁
    rw [mem_puncturedEnvelope]
    refine ⟨?_, ?_⟩
    · rw [← hQ]
      exact abs_le.mpr ⟨by linarith [hbox.1], by linarith [hbox.2]⟩
    · intro hq
      by_contra hcon
      push_neg at hcon
      exact hαmaj ⟨b₁, a₁, hc₁.1, hq, hc₁.2.2.1, hc₁.2.2.2.1, hc₁.2.2.2.2, hcon⟩
  · right
    change α - (a₂:ℝ)/b₂ ∈ puncturedEnvelope N Y H B b₂
    rw [mem_puncturedEnvelope]
    refine ⟨?_, ?_⟩
    · rw [← hQ]
      exact abs_le.mpr ⟨by linarith [hbox.1], by linarith [hbox.2]⟩
    · intro hq
      by_contra hcon
      push_neg at hcon
      exact hαmaj ⟨b₂, a₂, hc₂.1, hq, hc₂.2.2.1, hc₂.2.2.2.1, hc₂.2.2.2.2, hcon⟩

/-- Translation invariance for any measurable local rational envelope. -/
theorem envelope_translation (f : ℝ → ℝ) (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in {x : ℝ | x - c ∈ S}, f x) = ∫ t in S, f (c + t) := by
  classical
  have hpre : MeasurableSet {x : ℝ | x - c ∈ S} := hS.preimage (by fun_prop)
  rw [← integral_indicator hpre, ← integral_indicator hS]
  have heq : (fun t : ℝ => ({x : ℝ | x - c ∈ S}.indicator f) (c + t)) =
      S.indicator (fun t => f (c + t)) := by
    funext t
    change (if c + t - c ∈ S then f (c + t) else 0) =
      (if t ∈ S then f (c + t) else 0)
    rw [add_sub_cancel_left]
  rw [← heq, integral_add_left_eq_self]

/-- The exact local integral reduction follows from the two envelope cover.
CONDITIONAL ON farey_two_envelope_cover. -/
theorem local_reduction_from_cover :
    ∃ N₀ : ℝ, ∀ N Y H B P R : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
      0 ≤ P → 0 ≤ R →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H → principalArcMass N Y H B q ≤ P) →
      (∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H →
        1 ≤ a → a ≤ q → Nat.Coprime a q → remainderArcMass N Y H B q a ≤ R) →
      ∀ ξ : ℝ, localMass N Y H B ξ ≤ 4 * (P + R) := by
  obtain ⟨N₀, hcover⟩ := farey_two_envelope_cover
  refine ⟨N₀, ?_⟩
  intro N Y H B P R hN hY hH hB hP0 hR0 hP hR ξ
  obtain ⟨q₁, a₁, q₂, a₂, h₁, h₂, hc⟩ := hcover N Y H B hN hY hH hB ξ
  have hmeas (q : ℕ) : MeasurableSet (puncturedEnvelope N Y H B q) := by
    unfold puncturedEnvelope
    apply MeasurableSet.diff measurableSet_Icc
    split_ifs <;> measurability
  have hbound (q a : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ fareyOrder H)
      (ha : 1 ≤ a) (haq : a ≤ q) (hcop : Nat.Coprime a q) :
      (∫ x in {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q}, ‖secondSum Y x‖ ^ 2)
        ≤ 2 * (P + R) := by
    rw [envelope_translation _ _ _ (hmeas q)]
    have ht := arc_mass_from_parts N Y H B q a
    have hp := hP q hq hqQ
    have hr := hR q a hq hqQ ha haq hcop
    linarith
  have hint (q a : ℕ) : IntegrableOn (fun x : ℝ => ‖secondSum Y x‖ ^ 2)
      {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q} volume := by
    have hsub : {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q} ⊆
        Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * fareyOrder H))
          ((a : ℝ) / q + 1 / ((q : ℝ) * fareyOrder H)) := by
      intro x hx
      have hb := hx.1
      constructor <;> linarith [hb.1, hb.2]
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondSum phase
    fun_prop
  have hresult := two_piece_mass_bound volume
    ((hmeas q₁).preimage (by fun_prop : Measurable (fun x : ℝ => x - (a₁ : ℝ) / q₁)))
    (hint q₁ a₁) (hint q₂ a₂) (fun _ => sq_nonneg _) hc
    (hbound q₁ a₁ h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2)
    (hbound q₂ a₂ h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 h₂.2.2.2.2)
  calc localMass N Y H B ξ ≤ 2 * (2 * (P + R)) := hresult
    _ = 4 * (P + R) := by ring

#print axioms two_piece_mass_bound
#print axioms arc_mass_from_parts
#print axioms farey_two_envelope_cover
#print axioms envelope_translation
#print axioms local_reduction_from_cover
end
end LeanLab.Languasco2004.RationalGlue489
