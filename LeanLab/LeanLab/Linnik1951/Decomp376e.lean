/-
P0093 pages 165 and 166. Convert the entropy interval cover to doubled rational systems.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357c
import LeanLab.Linnik1951.Decomp111b
import LeanLab.Linnik1951.Measure435

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 165 Lemma 5 and the fixed eta choice at the start
of Section 8. The large T set has a finite interval cover with at most
A N to one hundredth intervals. Their lengths are at most one over tau
squared for tau equal to N to one seventh and sufficiently large N.
This leaf has no rational approximation or prime square integral. -/
theorem large_value_intervals376 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ I : Finset (ℝ × ℝ),
        (I.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ p ∈ I, p.2 - p.1 ≤ 1 / ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2) ∧
        {α : ℝ | α ∈ Set.Icc 0 1 ∧
          (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ⊆
          ⋃ p ∈ I, Set.Icc p.1 p.2 := by
  exact large_value_intervals435

/-- P0093 page 166 proof of Lemma 6. Retain the upper denominator
bound supplied by Dirichlet approximation, as well as the lower bound
from exclusion of the major arcs. -/
theorem interval_system_bounded376 (Q τ l u : ℝ) (hτ : 1 ≤ τ)
    (hlen : u - l ≤ 1 / τ ^ 2)
    (hmeet : (Set.Icc l u ∩ minorArcs111 Q τ).Nonempty) :
    ∃ q : ℕ, Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      Set.Icc l u ∩ minorArcs111 Q τ ⊆ arcSystem111 q τ := by
  obtain ⟨x, hx, hminor⟩ := hmeet
  obtain ⟨r, hden, hr⟩ := dirichlet_cover111 x τ hτ
  have hτp : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hdenp : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hQ : Q < (r.den : ℝ) := by
    by_contra h
    exact (hminor.2 r (le_of_not_gt h)).not_ge hr
  refine ⟨r.den, hQ.le, hden, ?_⟩
  intro y hy
  refine ⟨r, rfl, ?_⟩
  have hrad : 1 / τ ^ 2 ≤ 1 / ((r.den : ℝ) * τ) := by
    apply one_div_le_one_div_of_le (mul_pos hdenp hτp)
    nlinarith
  have hh := interval_double111 hx (hlen.trans hrad) hr hy.1
  simpa only [Set.mem_ofPred_eq, mul_one_div] using hh

/-- P0093 pages 166 and 167. Membership in the actual exceptional set
implies the rational minor arc condition used by Lemma 6. -/
theorem exceptional_subset_minor376 (N : ℕ) (η : ℝ) :
    exceptionalArcs280 N η ⊆
      minorArcs111 ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 7 : ℝ)) := by
  intro α hα
  refine ⟨hα.1, ?_⟩
  intro r hr
  apply lt_of_not_ge
  intro h
  exact hα.2.1 ⟨hα.1, r, hr, h⟩

/-- P0093 page 166 Lemma 6 applied to the interval cover from Lemma 5.
Exact exceptional_system_cover376 statement, CONDITIONAL only on the
entropy interval cover. The finite image cannot increase the cover count. -/
theorem exceptional_system_cover_proved376 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ S : Finset ℕ,
        (S.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ q ∈ S, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        exceptionalArcs280 N η ⊆
          ⋃ q ∈ S, arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1 := by
  classical
  obtain ⟨η, hη, hη1, A, hA, N0, hI⟩ := large_value_intervals376
  refine ⟨η, hη, hη1, A, hA, max 1 N0, ?_⟩
  intro N hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hτ : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  obtain ⟨I, hcard, hlen, hcover⟩ := hI N hN0
  let Q := (N : ℝ) ^ (1 / 10 : ℝ)
  let τ := (N : ℝ) ^ (1 / 7 : ℝ)
  let J := I.filter fun p => (Set.Icc p.1 p.2 ∩ minorArcs111 Q τ).Nonempty
  have hex (p : {p // p ∈ J}) : ∃ q : ℕ, Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      Set.Icc p.val.1 p.val.2 ∩ minorArcs111 Q τ ⊆ arcSystem111 q τ := by
    have hp := Finset.mem_filter.mp p.property
    exact interval_system_bounded376 Q τ p.val.1 p.val.2 hτ (hlen _ hp.1) hp.2
  choose q hq using hex
  let S : Finset ℕ := Finset.univ.image q
  refine ⟨S, ?_, ?_, ?_⟩
  · have hSJ : S.card ≤ J.card := by
      calc
        _ ≤ (Finset.univ : Finset {p // p ∈ J}).card := Finset.card_image_le
        _ = J.card := by simp
    have hJI : J.card ≤ I.card := Finset.card_filter_le _ _
    have hS := hSJ.trans hJI
    exact (show (S.card : ℝ) ≤ I.card by exact_mod_cast hS).trans hcard
  · intro d hd
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨(hq p).1, (hq p).2.1⟩
  · intro α hα
    have hlarge : α ∈ {α : ℝ | α ∈ Set.Icc 0 1 ∧
        (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} := ⟨hα.1, hα.2.2⟩
    obtain ⟨p, hp, hαp⟩ := Set.mem_iUnion₂.mp (hcover hlarge)
    have hm := exceptional_subset_minor376 N η hα
    have hpJ : p ∈ J := Finset.mem_filter.mpr ⟨hp, α, hαp, hm⟩
    let pJ : {p // p ∈ J} := ⟨p, hpJ⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨q pJ, Finset.mem_image.mpr ⟨pJ, Finset.mem_univ _, rfl⟩, ?_⟩
    exact ⟨(hq pJ).2.2 ⟨hαp, hm⟩, hα.1⟩

end LeanLab.Linnik1951
