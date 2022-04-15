import Lean
import FxyLang

open Lean

def run (f : String) (fast : Bool) : IO Unit := do
  let code ← IO.FS.readFile ⟨f⟩
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `FxyLang.Parser }] {}
  match ← parse code env with
  | (none    , p) =>
    match if fast then p.run! else p.run with
    | (_, er@(.err ..)) => IO.eprintln er
    | _                 => return
  | (some msg, _) => IO.eprintln msg

def help : String :=
"Usage: fxy COMMAND [ARGS]

Commands:
  run file.fxy            Runs the verified interpreter
  run! file.fxy           Runs the unverified interpreter (faster)
  repl                    Starts the interactive verified interpreter
  repl!                   Starts the interactive unverified interpreter (faster)
  format src.fxy tgt.fxy  Formats src.fxy and writes the result to tgt.fxy
  compile src.fxy tgt     Compiles src.fxy to a binary"

def main : List String → IO Unit
  | ["run", f] => run f Bool.false
  | ["run!", f] => run f Bool.true
  | ["repl"] => IO.println "WIP"
  | ["repl!"] => IO.println "WIP"
  | ["format", f, f'] => IO.println "WIP"
  | ["compile", f, f'] => IO.println "WIP"
  | _ => IO.println help
