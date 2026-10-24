import CategoricalInfluenceDiagramsProofs.Certificate.Composition
import CategoricalInfluenceDiagramsProofs.Certificate.Colimit
import CategoricalInfluenceDiagramsProofs.Certificate.Cli

/-!
# `lake exe check_composition PATH [--tol τ]`

Reads an `OpenInfluence.CompositionCertificate/v1`, `OpenInfluence.TensorCertificate/v1` or
`OpenInfluence.ColimitCertificate/v1` file (by its format string), decodes its reward
certificates with the decoder of `Certificate/Json.lean`, and decides `Composition.check τ`
or `Composition.checkTensor τ` of `Certificate/Composition.lean`, whose acceptance
`composition_sound_K`/`_W` and `tensor_sound_K`/`_W` prove sound, or `Colimit.check τ` of
`Certificate/Colimit.lean`, whose acceptance `colimit_sound_K`/`_W` prove exact. Exit status
and tolerance as for `check_certificate`.
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
      let colimitError ← match Json.readColimit text with
      | .error e => pure e
      | .ok cc => do
        IO.println s!"{colimitFormatName} ({cc.operation}): tolerance {showQ τ}"
        for (c, k) in cc.parts.zipIdx do
          IO.println s!"  part {k}: input rows {c.network.inputs.length}, output rows \
            {c.network.outputs.length}, {if c.check τ then "accepted" else "rejected"}"
        IO.println s!"  composite: input rows {cc.composite.network.inputs.length}, output \
          rows {cc.composite.network.outputs.length}, \
          {if cc.composite.check τ then "accepted" else "rejected"}"
        IO.println s!"  legs a colimit witness: {decide cc.Wired}"
        match cc.firstFailure τ with
        | none =>
          IO.println "accepted"
          return (0 : UInt32)
        | some stage =>
          IO.println s!"rejected: {stage}"
          return (1 : UInt32)
      match Json.readOperation text with
      | .error message =>
        IO.println s!"rejected: decode ({message}; nor a colimit certificate: {colimitError})"
        return (1 : UInt32)
      | .ok (isTensor, cc) =>
        let name := if isTensor then tensorFormatName else compositionFormatName
        IO.println s!"{name}: tolerance {showQ τ}"
        for (part, c) in [("left", cc.left), ("right", cc.right), ("composite", cc.composite)] do
          IO.println s!"  {part}: input rows {c.network.inputs.length}, output rows \
            {c.network.outputs.length}, {if c.check τ then "accepted" else "rejected"}"
        let valid := cc.left.network.check && cc.right.network.check &&
          cc.composite.network.check
        if isTensor then
          if h : cc.TensorAligned then
            if valid then
              IO.println s!"  largest tensor K gap: {showQ (Composition.tensorKError h)}"
              IO.println s!"  largest tensor W gap: {showQ (Composition.tensorWError h)}"
        else
          if h : cc.Aligned then
            if valid then
              IO.println s!"  largest composition K gap: {showQ (Composition.compKError h)}"
              IO.println s!"  largest composition W gap: {showQ (Composition.compWError h)}"
        match (if isTensor then cc.firstFailureTensor τ else cc.firstFailure τ) with
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
