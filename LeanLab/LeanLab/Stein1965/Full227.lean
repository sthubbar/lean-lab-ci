/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Assemble the original prefix and the projected suffix certificate.
Pages 428 and 429. The corrected rerun count is 10580.
-/
import LeanLab.Stein1965.Assembly227

namespace LeanLab.Stein1965.Full227
open LeanLab.SteinStein1965
open LeanLab.Stein1965.WindowReplay227
open LeanLab.Stein1965.CoreBridge227
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000

noncomputable def fullTrace : List Nat := CoreCertificates227.trace044 ++ Assembly227.trace176

theorem seed_window_pack (cap : Nat) (hcap : 10 ≤ cap) :
    pack (Window227.window Replay3.bitSeed3 6 cap) = CoreCertificates227.initial227 := by
  have hb : 21 < 2 ^ (cap + 1 - 6) := by
    exact lt_of_lt_of_le (by decide : 21 < 2 ^ 5)
      (Nat.pow_le_pow_right (by decide) (by omega))
  change (([3, 5] : List Nat), ([] : List Nat), (40 : Nat),
    21 % 2 ^ (cap + 1 - 6)) = CoreCertificates227.initial227
  rw [Nat.mod_eq_of_lt hb]
  rfl

theorem final_view :
    (((sPrime 3 (10 ^ 7)).1.filter (· ≤ 10 ^ 7)).length, (sPrime 3 (10 ^ 7)).2) =
      (Data227.state176.1, Data227.state176.2.1) := by
  have hc := Assembly227.prefix176
  change CountCore227.smallReplay Assembly227.trace176 811032 10000000
    (CountCore227.project CoreCertificates227.state044 10000000) =
      some Data227.state176 at hc
  rw [CountCore227.smallReplay_project] at hc
  obtain ⟨t, ht, hp⟩ := Option.map_eq_some_iff.mp hc
  have hf : Core227.replay fullTrace 6 10000000 CoreCertificates227.initial227 = some t := by
    exact Core227.replay_join CoreCertificates227.trace044 Assembly227.trace176
      6 811032 10000000 CoreCertificates227.initial227 CoreCertificates227.state044 t
      (by rw [CoreCertificates227.span044]) CoreCertificates227.prefix044 ht
  have hm := replay_pack fullTrace 6 10000000 (Window227.window Replay3.bitSeed3 6 10000000)
  rw [seed_window_pack 10000000 (by decide)] at hm
  rw [hf] at hm
  obtain ⟨s, hs, hpack⟩ := Option.map_eq_some_iff.mp hm.symm
  have hlen : replayLength fullTrace = 4999998 := by
    change Core227.length (CoreCertificates227.trace044 ++ Assembly227.trace176) = _
    rw [CoreCheck227.length_append, CoreCertificates227.span044, Assembly227.span176]
  have hv := windowReplay_seed3_view fullTrace 4999997 s hlen hs
  have hp' : CountCore227.project (pack s) 10000000 = Data227.state176 :=
    by rw [hpack]; exact hp
  have hproj := congrArg (fun u : CountCore227.SmallState => (u.1, u.2.1)) hp'
  change ((s.basis.filter (· ≤ 10000000)).length, s.failures) = _ at hproj
  have himg := congrArg (fun st : List Nat × List Nat =>
    ((st.1.filter (· ≤ 10000000)).length, st.2)) hv
  exact himg.symm.trans hproj

/-- Pages 428 and 429: the original run has no failures through 10000000. -/
theorem no_failures : (sPrime 3 (10 ^ 7)).2 = [] := by
  exact (Prod.mk.inj final_view).2


/-- Page 429, the corrected rerun count for the original prime S-run. -/
theorem count : ((sPrime 3 (10 ^ 7)).1.filter (· ≤ 10 ^ 7)).length = 10580 := by
  exact (Prod.mk.inj final_view).1

end LeanLab.Stein1965.Full227
#print axioms LeanLab.Stein1965.Full227.final_view
#print axioms LeanLab.Stein1965.Full227.no_failures

#print axioms LeanLab.Stein1965.Full227.seed_window_pack

#print axioms LeanLab.Stein1965.Full227.count
