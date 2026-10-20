import CategoricalInfluenceDiagramsProofs.Certificate.Composition
import CategoricalInfluenceDiagramsProofs.Certificate.Cli

/-!
# `lake exe check_composition PATH [--tol τ]`

Reads an `OpenInfluence.CompositionCertificate/v1` file, decodes its three reward
certificates with the decoder of `Certificate/Json.lean`, and decides `Composition.check τ`
of `Certificate/Composition.lean`, whose acceptance `composition_sound_K` and
`composition_sound_W` prove sound. Exit status and tolerance as for `check_certificate`.
-/

open OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Cli

def compositionMain (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match parseArgs args with
  | none =>
    stderr.putStrLn "usage: check_composition PATH [--tol TOLERANCE]"
    return (2 : UInt32)
  | some (path, τ) =>
    try
      let text ← IO.FS.readFile path
      match Json.readComposition text with
      | .error message =>
        IO.println s!"rejected: decode ({message})"
        return (1 : UInt32)
      | .ok cc =>
        IO.println s!"{compositionFormatName}: tolerance {showQ τ}"
        for (part, c) in [("left", cc.left), ("right", cc.right), ("composite", cc.composite)] do
          IO.println s!"  {part}: input rows {c.network.inputs.length}, output rows \
            {c.network.outputs.length}, {if c.check τ then "accepted" else "rejected"}"
        if h : cc.Aligned then
          if cc.left.network.check && cc.right.network.check && cc.composite.network.check then
            IO.println s!"  largest composition K gap: {showQ (Composition.compKError h)}"
            IO.println s!"  largest composition W gap: {showQ (Composition.compWError h)}"
        match cc.firstFailure τ with
        | none =>
          IO.println "accepted"
          return (0 : UInt32)
        | some stage =>
          IO.println s!"rejected: {stage}"
          return (1 : UInt32)
    catch error =>
      stderr.putStrLn s!"cannot read certificate: {error}"
      return (2 : UInt32)

def main (args : List String) : IO UInt32 := compositionMain args
