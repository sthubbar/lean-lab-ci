import LeanLab.BS2022GRH.ChenThresholdGRH

namespace LeanLab.BS2022GRH.ChenThresholdGRH
open Real Finset Classical

-- Bridge: SA n equals the count over primes p of the sifting condition on n - p.
theorem SA_as_prime_count (n : ℕ) :
    U7153.SA n =
      ((range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n ∧
        ∀ r : ℕ, r.Prime → (r : ℝ) < U7153.zz n → ¬ r ∣ n → ¬ r ∣ (n - p))).card := by
  unfold U7153.SA U7153.Aset
  set s := (range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n) with hs
  have hinj : Set.InjOn (fun p => n - p) ↑s := by
    intro p hp q hq h
    simp only [hs, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    have hpn : p ≤ n := by omega
    have hqn : q ≤ n := by omega
    have h2 : n - p = n - q := h
    omega
  have hinj2 : Set.InjOn (fun p => n - p) ↑(s.filter (fun p => U7153.NoSmallP n (U7153.zz n) (n - p))) :=
    hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
  have h_eq_set : (s.image (fun p => n - p)).filter (U7153.NoSmallP n (U7153.zz n)) =
      (s.filter (fun p => U7153.NoSmallP n (U7153.zz n) (n - p))).image (fun p => n - p) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨p, hp, heq⟩ := h.1
      subst heq
      exact ⟨p, hp, h.2, rfl⟩
    · obtain ⟨p, hp, ha, heq⟩ := h
      subst heq
      exact ⟨⟨p, hp, rfl⟩, ha⟩
  rw [h_eq_set, Finset.card_image_of_injOn hinj2]
  congr 1
  ext p
  simp only [hs, Finset.mem_filter, Finset.mem_range, and_assoc, U7153.NoSmallP]

end LeanLab.BS2022GRH.ChenThresholdGRH
