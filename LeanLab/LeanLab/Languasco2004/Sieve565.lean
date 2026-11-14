/-
Jia 1996 pages 283 and 284, displays 60 and 63.
Source https://doi.org/10.4064/aa-77-3-207-287.
Exact finite cancellation with the sealed strict sieve convention.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.Sieve565
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Displays 60 and 63: sieve a finite set by primes below z that do not divide n. -/
def sieved (s : Finset ℕ) (n : ℕ) (z : ℝ) : Finset ℕ :=
  s.filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n → ¬ p ∣ a)

/-- Displays 60 and 63: the layer whose least offending prime is r. -/
def layer (s : Finset ℕ) (n r : ℕ) : Finset ℕ :=
  (sieved s n r).filter (fun a => r ∣ a)

/-- Displays 60 and 63: all possible removed primes with exact half open endpoints. -/
def cutPrimes (s : Finset ℕ) (n : ℕ) (z Z : ℝ) : Finset ℕ :=
  (range (s.sup id + 1)).filter
    (fun r : ℕ => r.Prime ∧ z ≤ (r : ℝ) ∧ (r : ℝ) < Z ∧ ¬ r ∣ n)

/-- Displays 60 and 63: the removed low cutoff contribution. -/
def lowLayers (s : Finset ℕ) (n : ℕ) (z Z : ℝ) : ℝ :=
  ∑ r ∈ cutPrimes s n z Z, ((layer s n r).card : ℝ)

/-- Displays 60 and 63: distinct least prime layers are disjoint. -/
theorem layers_disjoint (s : Finset ℕ) (n : ℕ) (z Z : ℝ) :
    (↑(cutPrimes s n z Z) : Set ℕ).PairwiseDisjoint (layer s n) := by
  intro p hp q hq hpq
  obtain ⟨_, hpp, _, _, hpn⟩ := mem_filter.mp hp
  obtain ⟨_, hqp, _, _, hqn⟩ := mem_filter.mp hq
  apply disjoint_left.mpr
  intro a hap haq
  obtain ⟨hap, hpa⟩ := mem_filter.mp hap
  obtain ⟨haq, hqa⟩ := mem_filter.mp haq
  have hps := (mem_filter.mp hap).2
  have hqs := (mem_filter.mp haq).2
  rcases lt_or_gt_of_ne hpq with h | h
  · exact hqs p hpp (by exact_mod_cast h) hpn hpa
  · exact hps q hqp (by exact_mod_cast h) hqn hqa

/-- Displays 60 and 63: the high cutoff set and the removed layers partition the low set. -/
theorem sieve_partition (s : Finset ℕ) (n : ℕ) (z Z : ℝ)
    (hs : ∀ a ∈ s, 0 < a) (hz : z ≤ Z) :
    sieved s n z = sieved s n Z ∪ (cutPrimes s n z Z).biUnion (layer s n) := by
  ext a
  constructor
  · intro ha
    by_cases hZ : a ∈ sieved s n Z
    · exact mem_union_left _ hZ
    · obtain ⟨has, hasieve⟩ := mem_filter.mp ha
      have hex : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < Z ∧ ¬ p ∣ n ∧ p ∣ a := by
        by_contra h
        apply hZ
        apply mem_filter.mpr
        refine ⟨has, ?_⟩
        intro p hp hpZ hpn hpa
        exact h ⟨p, hp, hpZ, hpn, hpa⟩
      let p := Nat.find hex
      obtain ⟨hpp, hpZ, hpn, hpa⟩ := Nat.find_spec hex
      have hpz : z ≤ (p : ℝ) := le_of_not_gt (fun h => hasieve p hpp h hpn hpa)
      have hpcap : p < s.sup id + 1 := by
        have hpa' := Nat.le_of_dvd (hs a has) hpa
        have hacap : a ≤ s.sup id := le_sup (f := id) has
        omega
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_range.mpr hpcap, hpp, hpz, hpZ, hpn⟩, ?_⟩
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨has, ?_⟩, hpa⟩
      intro q hq hqp hqn hqa
      have hqp' : q < p := by exact_mod_cast hqp
      exact Nat.find_min hex hqp' ⟨hq, hqp.trans hpZ, hqn, hqa⟩
  · intro ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨has, h⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨has, fun p hp hpz => h p hp (hpz.trans_le hz)⟩
    · obtain ⟨p, hp, hap⟩ := mem_biUnion.mp ha
      obtain ⟨_, _, hpz, _, _⟩ := mem_filter.mp hp
      obtain ⟨hap, _⟩ := mem_filter.mp hap
      obtain ⟨has, h⟩ := mem_filter.mp hap
      exact mem_filter.mpr ⟨has, fun q hq hqz => h q hq (hqz.trans_le hpz)⟩

/-- Display 60 and the cancellation after 63: the low cutoff disappears exactly. -/
theorem low_cutoff_cancellation (s : Finset ℕ) (n : ℕ) (z Z : ℝ)
    (hs : ∀ a ∈ s, 0 < a) (hz : z ≤ Z) :
    ((sieved s n z).card : ℝ) - lowLayers s n z Z = ((sieved s n Z).card : ℝ) := by
  have hd : Disjoint (sieved s n Z) ((cutPrimes s n z Z).biUnion (layer s n)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨p, hp, hap⟩ := mem_biUnion.mp hb
    obtain ⟨_, hpp, _, hpZ, hpn⟩ := mem_filter.mp hp
    obtain ⟨_, hpa⟩ := mem_filter.mp hap
    exact (mem_filter.mp ha).2 p hpp hpZ hpn hpa
  have hc := congrArg Finset.card (sieve_partition s n z Z hs hz)
  rw [card_union_of_disjoint hd, card_biUnion (layers_disjoint s n z Z)] at hc
  have hr : ((sieved s n z).card : ℝ) = ((sieved s n Z).card : ℝ) + lowLayers s n z Z := by
    unfold lowLayers
    exact_mod_cast hc
  linarith

/-- Displays 58 to 60: two approximate transfers retain only the sum of their errors. -/
theorem transfer_cancellation (s : Finset ℕ) (n : ℕ) (z Z k A R e₁ e₂ : ℝ)
    (hs : ∀ a ∈ s, 0 < a) (hz : z ≤ Z)
    (hA : |A - k * ((sieved s n z).card : ℝ)| ≤ e₁)
    (hR : |R - k * lowLayers s n z Z| ≤ e₂) :
    |(A - R) - k * ((sieved s n Z).card : ℝ)| ≤ e₁ + e₂ := by
  have heq := low_cutoff_cancellation s n z Z hs hz
  calc |(A - R) - k * ((sieved s n Z).card : ℝ)| =
      |(A - k * ((sieved s n z).card : ℝ)) - (R - k * lowLayers s n z Z)| := by
        congr 1
        rw [← heq]
        ring
       _ ≤ |A - k * ((sieved s n z).card : ℝ)| + |R - k * lowLayers s n z Z| := abs_sub _ _
       _ ≤ e₁ + e₂ := add_le_add hA hR

/-- A genuine removed layer occurs for the singleton integer six and the prime two. -/
theorem cancellation_instance :
    ((sieved {6} 1 2).card : ℝ) = 1 ∧ lowLayers {6} 1 2 3 = 1 ∧
      ((sieved {6} 1 3).card : ℝ) = 0 := by
  have h2 : sieved {6} 1 2 = {6} := by
    ext a
    simp only [sieved, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · intro ha
      refine ⟨ha, ?_⟩
      intro p hp hp2
      have hp2' : p < 2 := by exact_mod_cast hp2
      have := hp.two_le
      omega
  have h3 : sieved {6} 1 3 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, hs⟩ := mem_filter.mp ha
    have ha6 : a = 6 := mem_singleton.mp ha
    subst a
    exact hs 2 (by decide) (by norm_num) (by norm_num) (by norm_num)
  have hc := low_cutoff_cancellation {6} 1 2 3
    (by intro a ha; have := mem_singleton.mp ha; omega) (by norm_num)
  rw [h2, h3] at hc
  norm_num at hc
  constructor
  · simp [h2]
  constructor
  · linarith
  · simp [h3]

/-- Displays 57 and 61: a common finite prime cap for the removed terms. -/
def boundedLayers (M : ℕ) (s : Finset ℕ) (n : ℕ) (z Z : ℝ) : ℝ :=
  ∑ r ∈ (range (M + 1)).filter
    (fun r : ℕ => r.Prime ∧ z ≤ (r : ℝ) ∧ (r : ℝ) < Z ∧ ¬ r ∣ n),
    ((layer s n r).card : ℝ)

/-- Displays 57 and 61: extending the prime cap adds only zero layers. -/
theorem lowLayers_eq_bounded (M : ℕ) (s : Finset ℕ) (n : ℕ) (z Z : ℝ)
    (hs : ∀ a ∈ s, 0 < a ∧ a ≤ M) :
    lowLayers s n z Z = boundedLayers M s n z Z := by
  have hsup : s.sup id ≤ M := Finset.sup_le (fun a ha => (hs a ha).2)
  unfold lowLayers boundedLayers
  apply sum_subset
  · intro r hr
    obtain ⟨hr, hp⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega), hp⟩
  · intro r hr hnot
    obtain ⟨hrM, hrp⟩ := mem_filter.mp hr
    have hlarge : s.sup id < r := by
      by_contra h
      apply hnot
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hrp⟩
    have hempty : layer s n r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha, hdiv⟩ := mem_filter.mp ha
      have has := (mem_filter.mp ha).1
      have hrle := Nat.le_of_dvd (hs a has).1 hdiv
      have hale : a ≤ s.sup id := le_sup (f := id) has
      omega
    simp [hempty]

/-- Display 61: the relaxed triple contribution at cutoff z. -/
def tripleSieved (M : ℕ) (s : Finset ℕ) (n : ℕ) (α Q z : ℝ) : ℝ :=
  ∑ r ∈ (range (M + 1)).filter
    (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < Q ∧ ¬ r ∣ n),
    ((sieved (s.filter (fun a => r ∣ a)) n z).card : ℝ)

/-- Display 63: the low cutoff terms removed from the triple contribution. -/
def tripleLayers (M : ℕ) (s : Finset ℕ) (n : ℕ) (α Q z : ℝ) : ℝ :=
  ∑ r ∈ (range (M + 1)).filter
    (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < Q ∧ ¬ r ∣ n),
    lowLayers (s.filter (fun a => r ∣ a)) n z α

/-- Display 61: replacing each prime cutoff r by α bounds the removed triple terms above. -/
theorem removed_le_triple (M : ℕ) (s : Finset ℕ) (n : ℕ) (α Q : ℝ) :
    boundedLayers M s n α Q ≤ tripleSieved M s n α Q α := by
  unfold boundedLayers tripleSieved
  apply sum_le_sum
  intro r hr
  obtain ⟨_, _, hαr, _, _⟩ := mem_filter.mp hr
  exact_mod_cast (card_le_card (show layer s n r ⊆ sieved (s.filter (fun a => r ∣ a)) n α from by
    intro a ha
    obtain ⟨ha, hdiv⟩ := mem_filter.mp ha
    obtain ⟨has, h⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨has, hdiv⟩,
      fun p hp hpα => h p hp (hpα.trans_le hαr)⟩))

/-- Displays 62 and 63: the triple low cutoff terms cancel without an error term. -/
theorem triple_cancellation (M : ℕ) (s : Finset ℕ) (n : ℕ) (α Q z : ℝ)
    (hs : ∀ a ∈ s, 0 < a) (hz : z ≤ α) :
    tripleSieved M s n α Q z - tripleLayers M s n α Q z =
      tripleSieved M s n α Q α := by
  unfold tripleSieved tripleLayers
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro r hr
  exact low_cutoff_cancellation _ n z α (fun a ha => hs a (mem_filter.mp ha).1) hz

/-- Displays 57 to 63: finite Buchstab subtraction gives the source lower bound before transfer. -/
theorem buchstab_lower (M : ℕ) (s : Finset ℕ) (n : ℕ) (z α Q : ℝ)
    (hs : ∀ a ∈ s, 0 < a ∧ a ≤ M) (hz : z ≤ α) (hQ : α ≤ Q) :
    ((sieved s n z).card : ℝ) - lowLayers s n z α -
      (tripleSieved M s n α Q z - tripleLayers M s n α Q z) ≤
        ((sieved s n Q).card : ℝ) := by
  rw [low_cutoff_cancellation s n z α (fun a ha => (hs a ha).1) hz,
    triple_cancellation M s n α Q z (fun a ha => (hs a ha).1) hz]
  have hc := low_cutoff_cancellation s n α Q (fun a ha => (hs a ha).1) hQ
  rw [lowLayers_eq_bounded M s n α Q hs] at hc
  have ht := removed_le_triple M s n α Q
  linarith

#print axioms lowLayers_eq_bounded
#print axioms removed_le_triple
#print axioms triple_cancellation
#print axioms buchstab_lower
#print axioms layers_disjoint
#print axioms sieve_partition
#print axioms low_cutoff_cancellation
#print axioms transfer_cancellation
#print axioms cancellation_instance
end
end LeanLab.Languasco2004.Sieve565
