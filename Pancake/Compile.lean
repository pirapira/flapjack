import Pancake.PanToCrep

/-!
Core statement lowering from Pancake to Crepe.

This is the structured-local/control-flow portion of `pan_to_crep`. The
function is intentionally extraction-friendly: malformed shape lengths and
front-end constructs whose runtime environments are not ported yet lower to
`Skip`, matching the reference pass's defensive fallback style.
-/

namespace Pancake

def compileProg [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (program : Prog α) : CrepProg α :=
  match program with
  | .skip => .skip
  | .dec name shape value body =>
      let compiled := compileExp context value
      let names := (List.range (Shape.shapeSize shape)).map
        (fun offset => context.maxVar + 1 + offset)
      let nextContext := { context with
        vars := (name, (shape, names)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape }
      if names.length = compiled.1.length then
        nestedDecs names compiled.1 (compileProg nextContext body)
      else .skip
  | .assign .local name value =>
      match lookupInfo name context.vars, compileExp context value with
      | some (_, names), (expressions, _) =>
          if names.length = expressions.length then
            crepNestedSeq (names.zipWith (fun name expression => .assign name expression) expressions)
          else .skip
      | _, _ => .skip
  | .assign .global _ _ => .skip
  | .primitive name operator _ =>
      match lookupInfo name context.vars with
      | some (_, names) => .primitive names operator []
      | none => .skip
  | .store address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .store address value
      | _, _ => .skip
  | .store32 address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .store32 address value
      | _, _ => .skip
  | .storeByte address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .storeByte address value
      | _, _ => .skip
  | .seq first second => .seq (compileProg context first) (compileProg context second)
  | .ite condition thenBranch elseBranch =>
      match compileExp context condition with
      | (condition :: _, _) => .ite condition (compileProg context thenBranch)
          (compileProg context elseBranch)
      | _ => .skip
  | .while condition body =>
      match compileExp context condition with
      | (condition :: _, _) => .while condition (compileProg context body)
      | _ => .skip
  | .break => .break 0
  | .continue => .continue 0
  | .call _ _ _ => .skip
  | .decCall _ _ _ _ _ => .skip
  | .extCall _ _ _ _ _ => .skip
  | .raise _ _ => .skip
  | .return value => .return (compileExp context value).1
  | .shMemLoad _ _ _ _ => .skip
  | .shMemStore _ _ _ => .skip
  | .tick => .tick
  | .annot _ _ => .skip

termination_by structural program

theorem compileProg_skip [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .skip = .skip := by
  simp [compileProg]

theorem compileProg_seq [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (first second : Prog α) :
    compileProg context (.seq first second) =
      .seq (compileProg context first) (compileProg context second) := by
  simp [compileProg]

theorem compileProg_return [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (value : Exp α) :
    compileProg context (.return value) = .return (compileExp context value).1 := by
  simp [compileProg]

end Pancake
