/-
AI wrote this Lean code for CODEX task70.
Certificate generation is untrusted. Every generated equality is checked by the kernel.
The generator splits replaySeek into at most sixty event intervals per equality.
No native proof oracle is used.
-/
import LeanLab.SteinStein1965.Seek
import Lean.Elab.Tactic.Decide
import Lean.Meta.Eval

open Lean Meta Elab Command Term

namespace LeanLab.SteinStein1965

syntax (name := certifySeekCmd) "certify_seek " ident term:max term:max : command

@[command_elab certifySeekCmd] meta unsafe def elabCertifySeek : CommandElab
  | `(certify_seek $id:ident $chooseStx:term $gapsStx:term) => do
    let base := (← getCurrNamespace) ++ id.getId
    liftTermElabM do
      let natType := Lean.mkConst ``Nat
      let optNat := mkApp (Lean.mkConst ``Option [.zero]) natType
      let chooseTy ← mkArrow natType (← mkArrow optNat optNat)
      let chooseExpr ← elabTermAndSynthesize chooseStx (some chooseTy)
      let gapsExpr ← elabTermAndSynthesize gapsStx (some (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Nat)))
      let chooseType ← inferType chooseExpr
      let chooseFn ← evalExpr (ℕ → Option ℕ → Option ℕ) chooseType chooseExpr
      let gaps ← evalExpr (List ℕ) (← inferType gapsExpr) gapsExpr
      if gaps.isEmpty then throwError "certify_seek requires a nonempty trace"
      let isAExpr := mkApp (Lean.mkConst ``primeA) (toExpr (89 : ℕ))
      let stateType := Lean.mkConst ``BitState
      let optionStateType := mkApp (Lean.mkConst ``Option [.zero]) stateType
      let mut state := bitSeed89
      let mut stateExpr := Lean.mkConst ``bitSeed89
      let mut lo := 178
      let mut remaining := gaps
      let mut records : Array (List ℕ × ℕ × Expr × Expr × Expr) := #[]
      while !remaining.isEmpty do
        let chunk := remaining.take 60
        remaining := remaining.drop 60
        let some next := replaySeek (primeA 89) chooseFn chunk lo state
          | throwError "untrusted trace failed at target {lo}"
        let j := records.size
        let stateName := base.appendAfter s!"_state{j}"
        let nextValue := mkAppN (Lean.mkConst ``BitState.mk)
          #[toExpr next.basis, toExpr next.failures, toExpr next.bits, toExpr next.sums]
        addDecl (.defnDecl {
          name := stateName, levelParams := [], type := stateType,
          value := nextValue, hints := .regular 0, safety := .safe })
        let nextExpr := Lean.mkConst stateName
        let lhs := mkAppN (Lean.mkConst ``replaySeek) #[isAExpr, chooseExpr, toExpr chunk, toExpr lo, stateExpr]
        let rhs ← mkAppM ``Option.some #[nextExpr]
        let goal ← mkEq lhs rhs
        let proof ← mkDecideProof goal
        let proofName := base.appendAfter s!"_chunk{j}"
        -- addDecl invokes the kernel. The native result is only a proposed certificate.
        withOptions (Elab.async.set · false) do
          addDecl (.thmDecl { name := proofName, levelParams := [], type := goal, value := proof })
        resetCache
        records := records.push (chunk, lo, stateExpr, nextExpr, Lean.mkConst proofName)
        state := next
        stateExpr := nextExpr
        lo := lo + 2 * replayLength chunk
      let finalName := base.appendAfter "_result"
      addDecl (.defnDecl {
        name := finalName, levelParams := [], type := stateType,
        value := stateExpr, hints := .regular 0, safety := .safe })
      let mut suffixExpr := toExpr records[records.size - 1]!.1
      let mut proof := records[records.size - 1]!.2.2.2.2
      let lastState := stateExpr
      for off in [1:records.size] do
        let i := records.size - 1 - off
        let (chunk, start, previousExpr, nextExpr, chunkProof) := records[i]!
        let chunkExpr := toExpr chunk
        let nextStart := start + 2 * replayLength chunk
        let lenExpr := mkApp (Lean.mkConst ``replayLength) chunkExpr
        let scalar ← mkAppM ``Nat.add #[toExpr start, ← mkAppM ``Nat.mul #[toExpr (2 : ℕ), lenExpr]]
        let scalarGoal ← mkEq scalar (toExpr nextStart)
        let scalarProof ← mkDecideProof scalarGoal
        proof := mkAppN (Lean.mkConst ``replaySeek_join)
          #[isAExpr, chooseExpr, chunkExpr, suffixExpr, toExpr start, toExpr nextStart,
            previousExpr, nextExpr, lastState, scalarProof, chunkProof, proof]
        suffixExpr := mkAppN (Lean.mkConst ``List.append [.zero])
          #[Lean.mkConst ``Nat, chunkExpr, suffixExpr]
      let gapGoal ← mkEq suffixExpr gapsExpr
      let gapProof ← mkDecideProof gapGoal
      proof := mkAppN (Lean.mkConst ``replaySeek_transport)
        #[isAExpr, chooseExpr, suffixExpr, gapsExpr, toExpr (178 : ℕ),
          Lean.mkConst ``bitSeed89, lastState, gapProof, proof]
      let lhs := mkAppN (Lean.mkConst ``replaySeek)
        #[isAExpr, chooseExpr, gapsExpr, toExpr (178 : ℕ), Lean.mkConst ``bitSeed89]
      let rhs ← mkAppM ``Option.some #[Lean.mkConst finalName]
      let goal ← mkEq lhs rhs
      withOptions (Elab.async.set · false) do
        addDecl (.thmDecl { name := base, levelParams := [], type := goal, value := proof })
      logInfo m!"kernel checked {records.size} replaySeek certificates for {base}"
  | _ => throwUnsupportedSyntax

end LeanLab.SteinStein1965
