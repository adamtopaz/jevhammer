module

public meta import JevHammer.Tactics
public meta import JevHammer.Proof

public meta section
namespace JevHammer
open Lean Meta

/-! Components of the original adaptive tactic collection. Downstream packages
can reuse individual generators, extend them, or replace any phase entirely. -/
namespace DefaultTactics

def close : TacticGenerator := .fixed portfolioCodes
def prepare : TacticGenerator := .fixed #["intros"]
def cleanup : TacticGenerator := .fixed #["solve | assumption | rfl | trivial"]

def finish : TacticGenerator := fun ctx => do
  let mut codes := #[]
  for count in #[ctx.config.premiseCount, ctx.config.premiseCount * 2] do
    let ns := ctx.premises.take count
    unless ns.isEmpty do
      let printed ← ns.mapM fun name => return (← unresolveNameGlobal name).toString
      let args := String.intercalate ", " printed.toList
      codes := codes ++ #[s!"solve | simp_all [{args}]", s!"grind (gen := 8) [{args}]",
        s!"aesop (add unsafe 50% {String.intercalate " " printed.toList})" ++
          " (config := { maxRuleApplications := 160 })"]
  return codes

def basicSteps : TacticGenerator := .fixed
  #["simp_all", "intros", "constructor", "ext1", "contrapose!", "push_neg at *", "symm"]

private def relevantSymbol (n : Name) : Bool :=
  !([``Eq, ``Iff, ``And, ``Or, ``Not, ``Exists, ``True, ``False, ``Decidable,
     ``OfNat.ofNat, ``OfNat, ``Nat, ``Int].contains n) &&
  !n.isInternal && !n.toString.startsWith "Lean." && !n.toString.startsWith "JevPilot."

def unfoldSteps : TacticGenerator := fun ctx => do
  let mut codes := #[]
  let symbols := (← instantiateMVars (← ctx.goal.getType)).getUsedConstants.filter relevantSymbol
  for n in symbols.take 8 do
    if (← getConstInfo n).isDefinition then
      codes := codes ++ #[s!"unfold {n}", s!"simp_all only [{n}]"]
  return codes

private def localNames : MetaM (Array String) := do
  let mut names := #[]
  for h in ← getLCtx do
    if h.isImplementationDetail || h.userName.isInternal || names.size >= 8 then continue
    if ← isProp h.type then names := names.push h.userName.toString
  return names

def localApplySteps : TacticGenerator := fun _ => do
  return (← localNames).map fun n => s!"apply {n}"

def localCasesSteps : TacticGenerator := fun _ => do
  return (← localNames).map fun n => s!"cases {n}"

def localRewriteSteps : TacticGenerator := fun _ => do
  return (← localNames).flatMap fun n => #[s!"rw [{n}]", s!"rw [← {n}]"]

private def premiseNames (ctx : TacticContext) : MetaM (Array String) :=
  (ctx.premises.take 12).mapM fun n => return (← unresolveNameGlobal n).toString

def premiseApplySteps : TacticGenerator := fun ctx => do
  return (← premiseNames ctx).map fun n => s!"apply {n}"

def premiseRewriteSteps : TacticGenerator := fun ctx => do
  return (← premiseNames ctx).flatMap fun n => #[s!"rw [{n}]", s!"rw [← {n}]"]

def premiseSimpSteps : TacticGenerator := fun ctx => do
  return (← premiseNames ctx).map fun n => s!"simp only [{n}] at *"

/-- Preserve the adaptive engine's original round-robin action ordering. -/
def steps : TacticGenerator := .interleave #[basicSteps, premiseApplySteps,
  localApplySteps, premiseRewriteSteps, unfoldSteps, localCasesSteps,
  premiseSimpSteps, localRewriteSteps]

end DefaultTactics

/-- The standard collection, with optional Aesop/Mathlib steps attempted only
when their syntax is available. No extra package dependencies are introduced. -/
def defaultTactics : TacticSet := {
  close := DefaultTactics.close
  prepare := DefaultTactics.prepare
  finish := DefaultTactics.finish
  steps := DefaultTactics.steps
  cleanup := DefaultTactics.cleanup }

end JevHammer
